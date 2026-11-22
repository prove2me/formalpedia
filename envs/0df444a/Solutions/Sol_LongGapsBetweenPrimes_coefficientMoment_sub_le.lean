-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientMoment_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:47.629982+00:00
-- url     : https://prove2.me/submissions/8f87682b-18af-40b2-9152-e0cda1922390

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_one_lt_of_mem_divisors_erase_one
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_zero
import Theorems.Thm_LongGapsBetweenPrimes_rpow_sub_one_le
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_sq_mul_log

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : 1 < P) (γ : ℝ) :
    coefficientMoment P γ - coefficientMoment P 0 ≤
      (γ / normalizer P) * coefficientAbsMoment P γ := by
  rw [coefficientMoment, coefficientMoment_zero, ← Finset.sum_sub_distrib,
    ← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr (by omega : P ≠ 0))]
  simp only [Nat.cast_one, Real.one_rpow, Nat.totient_one, mul_one, div_one,
    sub_self, add_zero]
  unfold coefficientAbsMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hd' := one_lt_of_mem_divisors_erase_one hd
  calc
    coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient -
        coefficient P d ^ 2 / d.totient =
        coefficient P d ^ 2 * ((d : ℝ) ^ γ - 1) / d.totient := by ring
    _ ≤ coefficient P d ^ 2 * (γ * (d : ℝ) ^ γ * Real.log d) / d.totient :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (rpow_sub_one_le (by exact_mod_cast (zero_lt_one.trans hd'))) (sq_nonneg _))
        (Nat.cast_nonneg _)
    _ = (coefficient P d ^ 2 * Real.log d) * (γ * (d : ℝ) ^ γ) / d.totient := by ring
    _ = (γ / normalizer P) * (|coefficient P d| * (d : ℝ) ^ γ / d.totient) := by
      rw [coefficient_sq_mul_log hP hd']
      ring
end LongGapsBetweenPrimes
