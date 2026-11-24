-- Prove2me | solution 1 for M7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:43.22481+00:00
-- url     : https://prove2.me/submissions/8992e31d-7bdf-44b7-9538-c44fde5f68f0

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
public import Theorems.Thm_crazy7

set_option autoImplicit false
@[expose] public section
public section
open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
  IsCyclotomicExtension.Rat Polynomial cyclotomic Ideal
variable {K : Type*} [Field K] [NumberField K]
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)
variable [IsCyclotomicExtension {7} ℚ K]
theorem _root_.solution : ⌊(M K)⌋₊ = 4 := by
  rw [discr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 7, totient_prime
      Nat.prime_seven]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy7
