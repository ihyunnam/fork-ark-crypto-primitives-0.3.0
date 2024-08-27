use ark_ff::{BigInteger, BigInteger256, BitIteratorLE, Fp256, One};
use ark_ff::{
    bytes::{FromBytes, ToBytes},
    fields::{Field, PrimeField},
    UniformRand,
};
use super::sbox::constraints::SboxConstraints;
use super::PoseidonRoundParams;
use super::{Poseidon, CRH};
use crate::CRHGadget as CRHGadgetTrait;
// use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::uint8::UInt8;
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_r1cs_std::{alloc::AllocVar, fields::FieldVar, prelude::*};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::vec::Vec;

use crate::crh::TwoToOneCRHGadget;
use ark_std::borrow::ToOwned;
use ark_std::marker::PhantomData;
use core::borrow::Borrow;

#[derive(Derivative, Clone, Debug)]     // TODO: MUST REMOVE DEBUG
pub struct PoseidonRoundParamsVar<F: PrimeField, P: PoseidonRoundParams<F>> {
    pub params: Poseidon<F, P>,     // TODO: MUST REMOVE PUB
}

pub struct CRHGadget<F: PrimeField, P: PoseidonRoundParams<F>> {
    field: PhantomData<F>,
    params: PhantomData<PoseidonRoundParamsVar<F, P>>,
}

impl<F: PrimeField, P: PoseidonRoundParams<F>> PoseidonRoundParamsVar<F, P> {
    fn permute(&self, input: Vec<FpVar<F>>) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let width = P::WIDTH;
        assert_eq!(input.len(), width);

        let full_rounds_beginning = P::FULL_ROUNDS_BEGINNING;
        //println!("PERMUTE FULL ROUNDS BEGINNING GADGET {:?}", full_rounds_beginning);
        let partial_rounds = P::PARTIAL_ROUNDS;
        let full_rounds_end = P::FULL_ROUNDS_END;

        let mut input_vars: Vec<FpVar<F>> = input;

        let mut round_keys_offset = 0;

        // ------------ First rounds with full SBox begin --------------------

        for _k in 0..full_rounds_beginning {
            // TODO: Check if Scalar::default() can be replaced by FpVar<F>::one() or FpVar<F>::zero()
            let mut sbox_outputs: Vec<FpVar<F>> = vec![FpVar::<F>::zero(); width];

            // Substitution (S-box) layer
            for i in 0..width {
                let round_key = self.params.round_keys[round_keys_offset];
                sbox_outputs[i] = P::SBOX
                    .synthesize_sbox(input_vars[i].clone(), round_key)?
                    .into();

                round_keys_offset += 1;
            }

            // TODO: Check if Scalar::default() can be replaced by FpVar<F>::one()
            let mut next_input_vars: Vec<FpVar<F>> = vec![FpVar::<F>::zero(); width];

            self.apply_linear_layer(
                width,
                sbox_outputs,
                &mut next_input_vars,
                &self.params.mds_matrix,
            );

            for i in 0..width {
                // replace input_vars with next_input_vars
                input_vars[i] = next_input_vars.remove(0);
            }
        }

        //println!("PERMUTE OUTPUT OF FIRST ROUND, GADGET {:?}", input_vars.value());

        // ------------ First rounds with full SBox begin --------------------

        // ------------ Middle rounds with partial SBox begin --------------------

        for _k in full_rounds_beginning..(full_rounds_beginning + partial_rounds) {
            let mut sbox_outputs: Vec<FpVar<F>> = vec![FpVar::<F>::zero(); width];

            // Substitution (S-box) layer
            for i in 0..width {
                let round_key = self.params.round_keys[round_keys_offset];

                // apply Sbox to only 1 element of the state.
                // Here the last one is chosen but the choice is arbitrary.
                if i == width - 1 {
                    sbox_outputs[i] = P::SBOX
                        .synthesize_sbox(input_vars[i].clone(), round_key)?
                        .into();
                } else {
                    sbox_outputs[i] = input_vars[i].clone() + round_key;
                }

                round_keys_offset += 1;
            }

            // Linear layer
            // TODO: Check if Scalar::default() can be replaced by FpVar<F>::one()
            let mut next_input_vars: Vec<FpVar<F>> = vec![FpVar::<F>::zero(); width];

            self.apply_linear_layer(
                width,
                sbox_outputs,
                &mut next_input_vars,
                &self.params.mds_matrix,
            );

            for i in 0..width {
                // replace input_vars with simplified next_input_vars
                input_vars[i] = next_input_vars.remove(0);
            }
        }

        // ------------ Middle rounds with partial SBox end --------------------

        // ------------ Last rounds with full SBox begin --------------------

        //println!("PERMUTE OUTPUT OF MIDDLE ROUND, GADGET {:?}", input_vars.value());

        for _k in (full_rounds_beginning + partial_rounds)
            ..(full_rounds_beginning + partial_rounds + full_rounds_end)
        {
            // TODO: Check if Scalar::default() can be replaced by FpVar<F>::one()
            let mut sbox_outputs: Vec<FpVar<F>> = vec![FpVar::<F>::zero(); width];

            // Substitution (S-box) layer
            for i in 0..width {
                let round_key = self.params.round_keys[round_keys_offset];
                sbox_outputs[i] = P::SBOX
                    .synthesize_sbox(input_vars[i].clone(), round_key)?
                    .into();

                round_keys_offset += 1;
            }

            // Linear layer
            // TODO: Check if Scalar::default() can be replaced by FpVar<F>::one()
            let mut next_input_vars: Vec<FpVar<F>> = vec![FpVar::<F>::zero(); width];

            self.apply_linear_layer(
                width,
                sbox_outputs,
                &mut next_input_vars,
                &self.params.mds_matrix,
            );

            for i in 0..width {
                // replace input_vars with next_input_vars
                input_vars[i] = next_input_vars.remove(0);
            }
        }

        // ------------ Last rounds with full SBox end --------------------

        //println!("PERMUTE OUTPUT, GADGET {:?}", input_vars.value());

        Ok(input_vars)
    }

    fn apply_linear_layer(
        &self,
        width: usize,
        sbox_outs: Vec<FpVar<F>>,
        next_inputs: &mut Vec<FpVar<F>>,
        mds_matrix: &Vec<Vec<F>>,
    ) {
        for j in 0..width {
            for i in 0..width {
                next_inputs[i] = next_inputs[i].clone()
                    + sbox_outs[j].clone() * &FpVar::<F>::Constant(mds_matrix[i][j]);
            }
        }
    }

    fn hash_2(
        &self,
        xl: FpVar<F>,
        xr: FpVar<F>,
        statics: Vec<FpVar<F>>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let width = P::WIDTH;
        // println!("WIDTH INSIDE HASH 2, GADGET {:?}", width);     // WIDTH ALL SAME
        // Only 2 inputs to the permutation are set to the input of this hash
        // function.
        assert_eq!(statics.len(), width - 2);

        // Always keep the 1st input as 0
        let mut inputs = vec![statics[0].to_owned()];
        inputs.push(xl);
        inputs.push(xr);

        // statics correspond to committed variables with values as PADDING_CONST
        // and 0s and randomness as 0
        for i in 1..statics.len() {
            inputs.push(statics[i].to_owned());
        }
        let permutation_output = self.permute(inputs)?;

        //println!("HASH 2 permuation output, GADGET {:?}", permutation_output[1].value());
        Ok(permutation_output[1].clone())
    }

    fn hash_4(
        &self,
        input: &[FpVar<F>],
        statics: Vec<FpVar<F>>,
    ) -> Result<FpVar<F>, SynthesisError> {
        assert_eq!(input.len(), 4);
        let width = P::WIDTH;
        //println!("WIDTH INSIDE HASH 4, GADGET {:?}", width);
        // Only 4 inputs to the permutation are set to the input of this hash
        // function.
        assert_eq!(statics.len(), width - 4);
        // Always keep the 1st input as 0
        let mut inputs = vec![statics[0].to_owned()];
        inputs.push(input[0].clone());
        inputs.push(input[1].clone());
        inputs.push(input[2].clone());
        inputs.push(input[3].clone());

        // statics correspond to committed variables with values as PADDING_CONST
        // and 0s and randomness as 0
        for i in 1..statics.len() {
            inputs.push(statics[i].to_owned());
        }

        let permutation_output = self.permute(inputs)?;
        //println!("HASH 4 permuation output, GADGET {:?}", permutation_output[1].value());

        Ok(permutation_output[1].to_owned())
    }
}

// https://github.com/arkworks-rs/r1cs-std/blob/master/src/bits/uint8.rs#L343
impl<F: PrimeField, P: PoseidonRoundParams<F>> CRHGadgetTrait<CRH<F, P>, F> for CRHGadget<F, P> {
    type OutputVar = FpVar<F>;
    type ParametersVar = PoseidonRoundParamsVar<F, P>;

    fn evaluate(
        parameters: &Self::ParametersVar,
        input: &[UInt8<F>],
    ) -> Result<Self::OutputVar, SynthesisError> {
        let f_var_vec: Vec<FpVar<F>> = input.to_constraint_field()?;
        println!("F VAR VEC LEN {:?}", f_var_vec.len());
        
        // Choice is arbitrary
        let padding_const: F = F::from(101u32);
        let zero_const: F = F::zero();

        let len_is_2 = Boolean::constant(f_var_vec.len() == 2);
        let len_is_4 = Boolean::constant(f_var_vec.len() == 4);
        let valid_len = len_is_2.or(&len_is_4).unwrap();

        // Enforce that `f_var_vec.len()` must be 2 or 4
        valid_len.enforce_equal(&Boolean::TRUE).unwrap();  // This will fail the circuit if the length is not 2 or 4

        // Precompute the possible `statics` values for each case
        let statics_len_2 = vec![
            FpVar::<F>::Constant(zero_const),
            FpVar::<F>::Constant(padding_const),
            FpVar::<F>::Constant(zero_const),
            FpVar::<F>::Constant(zero_const),
        ];

        let statics_len_4 = vec![
            FpVar::<F>::Constant(zero_const),
            FpVar::<F>::Constant(padding_const),
        ];

        // Conditionally select the correct `statics` based on `len_is_2`
        let statics = len_is_2
            .conditionally_select(
                &FpVar::constant_vector(statics_len_2),
                &FpVar::constant_vector(statics_len_4),
            )
            .unwrap(); // Handle potential errors appropriately

        // Precompute the possible results for each case
        let result_len_2 = parameters.hash_2(
            f_var_vec[0].clone(),
            f_var_vec[1].clone(),
            statics.clone(),
        );

        let result_len_4 = parameters.hash_4(&f_var_vec, statics.clone());

        // Conditionally select the correct `result` based on `len_is_2`
        let result = len_is_2
            .conditionally_select(&result_len_2, &result_len_4)
            .unwrap();

        
        //println!("F VAR VEC {:?}", f_var_vec.value());
        // let statics = match f_var_vec.len() {
        //     2 => {
        //         vec![
        //             FpVar::<F>::Constant(zero_const),
        //             FpVar::<F>::Constant(padding_const),
        //             FpVar::<F>::Constant(zero_const),
        //             FpVar::<F>::Constant(zero_const),
        //         ]
        //     }
        //     4 => {
        //         vec![
        //             FpVar::<F>::Constant(zero_const),
        //             FpVar::<F>::Constant(padding_const),
        //         ]
        //     }
        //     _ => panic!("incorrect number (elements) for poseidon hash"),
        // };

        // let result = match f_var_vec.len() {
        //     2 => parameters.hash_2(f_var_vec[0].clone(), f_var_vec[1].clone(), statics),
        //     4 => parameters.hash_4(&f_var_vec, statics),
        //     _ => panic!("incorrect number (elements) for poseidon hash"),
        // };

        Ok(result.unwrap_or(Self::OutputVar::zero()))
    }
}

impl<F: PrimeField, P: PoseidonRoundParams<F>> TwoToOneCRHGadget<CRH<F, P>, F> for CRHGadget<F, P> {
    type OutputVar = FpVar<F>;
    type ParametersVar = PoseidonRoundParamsVar<F, P>;

    fn evaluate(
        parameters: &Self::ParametersVar,
        left_input: &[UInt8<F>],
        right_input: &[UInt8<F>],
    ) -> Result<Self::OutputVar, SynthesisError> {
        // assume equality of left and right length
        assert_eq!(left_input.len(), right_input.len());
        let chained_input: Vec<_> = left_input
            .to_vec()
            .into_iter()
            .chain(right_input.to_vec().into_iter())
            .collect();
        <Self as CRHGadgetTrait<_, _>>::evaluate(parameters, &chained_input)
    }
}

impl<F: PrimeField, P: PoseidonRoundParams<F>> AllocVar<Poseidon<F, P>, F>
    for PoseidonRoundParamsVar<F, P>
{
    #[tracing::instrument(target = "r1cs", skip(_cs, f))]
    fn new_variable<T: Borrow<Poseidon<F, P>>>(
        _cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let params = f()?.borrow().clone();
        Ok(Self { params })
    }
}

/* ADDED BY ME. ADOPTED FROM ARK-CRYPTO-PRIMITIVES 0.4.0 POSEIDON. */

pub fn find_poseidon_ark_and_mds<F: PrimeField>(
    prime_bits: u64,
    rate: usize,
    full_rounds: u64,
    partial_rounds: u64,
    skip_matrices: u64,
) -> (Vec<Vec<F>>, Vec<Vec<F>>) {
    let mut lfsr = PoseidonGrainLFSR::new(
        false,
        prime_bits,
        (rate + 1) as u64,
        full_rounds,
        partial_rounds,
    );

    let mut ark = Vec::<Vec<F>>::with_capacity((full_rounds + partial_rounds) as usize);
    for _ in 0..(full_rounds + partial_rounds) {
        ark.push(lfsr.get_field_elements_rejection_sampling(rate + 1));
    }

    let mut mds = Vec::<Vec<F>>::with_capacity(rate + 1);
    mds.resize(rate + 1, vec![F::zero(); rate + 1]);
    for _ in 0..skip_matrices {
        let _ = lfsr.get_field_elements_mod_p::<F>(2 * (rate + 1));
    }

    // a qualifying matrix must satisfy the following requirements
    // - there is no duplication among the elements in x or y
    // - there is no i and j such that x[i] + y[j] = p
    // - the resultant MDS passes all the three tests

    let xs = lfsr.get_field_elements_mod_p::<F>(rate + 1);
    let ys = lfsr.get_field_elements_mod_p::<F>(rate + 1);

    for i in 0..(rate + 1) {
        for j in 0..(rate + 1) {
            mds[i][j] = (xs[i] + &ys[j]).inverse().unwrap_or(F::default());
        }
    }

    (ark, mds)
}

pub struct PoseidonGrainLFSR {
    pub prime_num_bits: u64,

    pub state: [bool; 80],
    pub head: usize,
}

#[allow(unused_variables)]
impl PoseidonGrainLFSR {
    pub fn new(
        is_sbox_an_inverse: bool,
        prime_num_bits: u64,
        state_len: u64,
        num_full_rounds: u64,
        num_partial_rounds: u64,
    ) -> Self {
        let mut state = [false; 80];

        // b0, b1 describes the field
        state[1] = true;

        // b2, ..., b5 describes the S-BOX
        if is_sbox_an_inverse {
            state[5] = true;
        } else {
            state[5] = false;
        }

        // b6, ..., b17 are the binary representation of n (prime_num_bits)
        {
            let mut cur = prime_num_bits;
            for i in (6..=17).rev() {
                state[i] = cur & 1 == 1;
                cur >>= 1;
            }
        }

        // b18, ..., b29 are the binary representation of t (state_len, rate + capacity)
        {
            let mut cur = state_len;
            for i in (18..=29).rev() {
                state[i] = cur & 1 == 1;
                cur >>= 1;
            }
        }

        // b30, ..., b39 are the binary representation of R_F (the number of full rounds)
        {
            let mut cur = num_full_rounds;
            for i in (30..=39).rev() {
                state[i] = cur & 1 == 1;
                cur >>= 1;
            }
        }

        // b40, ..., b49 are the binary representation of R_P (the number of partial rounds)
        {
            let mut cur = num_partial_rounds;
            for i in (40..=49).rev() {
                state[i] = cur & 1 == 1;
                cur >>= 1;
            }
        }

        // b50, ..., b79 are set to 1
        for i in 50..=79 {
            state[i] = true;
        }

        let head = 0;

        let mut res = Self {
            prime_num_bits,
            state,
            head,
        };
        res.init();
        res
    }

    pub fn get_bits(&mut self, num_bits: usize) -> Vec<bool> {
        let mut res = Vec::new();

        for _ in 0..num_bits {
            // Obtain the first bit
            let mut new_bit = self.update();

            // Loop until the first bit is true
            while new_bit == false {
                // Discard the second bit
                let _ = self.update();
                // Obtain another first bit
                new_bit = self.update();
            }

            // Obtain the second bit
            res.push(self.update());
        }

        res
    }

    /* MUST BE TRUE: F::MODULUS_BIT_SIZE as u64 == self.prime_num_bits */
    pub fn get_field_elements_rejection_sampling<F: PrimeField>(
        &mut self,
        num_elems: usize,
    ) -> Vec<F> {
        // assert_eq!(F::MODULUS_BIT_SIZE as u64, self.prime_num_bits);

        let mut res = Vec::new();
        for _ in 0..num_elems {
            // Perform rejection sampling
            loop {
                // Obtain n bits and make it most-significant-bit first
                let mut bits = self.get_bits(self.prime_num_bits as usize);
                bits.reverse();

                // Construct the number
                let bigint = F::BigInt::from_bits_le(&bits);

                if let Some(f) = F::from_repr(bigint) {
                    res.push(f);
                    break;
                }
            }
        }

        res
    }

    pub fn get_field_elements_mod_p<F: PrimeField>(&mut self, num_elems: usize) -> Vec<F> {
        // assert_eq!(F::MODULUS_BIT_SIZE as u64, self.prime_num_bits);

        let mut res = Vec::new();
        for _ in 0..num_elems {
            // Obtain n bits and make it most-significant-bit first
            let mut bits = self.get_bits(self.prime_num_bits as usize);
            bits.reverse();

            let bytes = bits
                .chunks(8)
                .map(|chunk| {
                    let mut result = 0u8;
                    for (i, bit) in chunk.iter().enumerate() {
                        result |= u8::from(*bit) << i
                    }
                    result
                })
                .collect::<Vec<u8>>();

            res.push(F::from_le_bytes_mod_order(&bytes));
        }

        res
    }

    #[inline]
    fn update(&mut self) -> bool {
        let new_bit = self.state[(self.head + 62) % 80]
            ^ self.state[(self.head + 51) % 80]
            ^ self.state[(self.head + 38) % 80]
            ^ self.state[(self.head + 23) % 80]
            ^ self.state[(self.head + 13) % 80]
            ^ self.state[self.head];
        self.state[self.head] = new_bit;
        self.head += 1;
        self.head %= 80;

        new_bit
    }

    fn init(&mut self) {
        for _ in 0..160 {
            let _ = self.update();
        }
    }
}
