-- Prove2me | solution 1 for LongGapsBetweenPrimes.weighted_diagonal_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:50.744982+00:00
-- url     : https://prove2.me/submissions/1c198b6a-1cf3-4908-bcaa-4cec592b545c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleMass_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_sum_tupleMass
import Theorems.Thm_LongGapsBetweenPrimes_sum_tupleMass_mul_rpow

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} {D a b γ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (v : DivisorTuple P k → ℝ)
    (hv : ∀ r ∈ tupleRegion P k D, v r ^ 2 ≤ a * (tupleProduct r : ℝ) ^ γ + b) :
    (∑ r ∈ tupleRegion P k D, tupleMass r * v r ^ 2) ≤
      a * coefficientMoment P γ ^ k + b * coefficientMoment P 0 ^ k := by
  classical
  calc
    _ ≤ ∑ r ∈ tupleRegion P k D,
        tupleMass r * (a * (tupleProduct r : ℝ) ^ γ + b) := by
      exact Finset.sum_le_sum fun r hr =>
        mul_le_mul_of_nonneg_left (hv r hr) (tupleMass_nonneg r)
    _ ≤ ∑ r : DivisorTuple P k,
        tupleMass r * (a * (tupleProduct r : ℝ) ^ γ + b) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro r _ _
      exact mul_nonneg (tupleMass_nonneg r)
        (add_nonneg (mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hb)
    _ = a * (∑ r : DivisorTuple P k, tupleMass r * (tupleProduct r : ℝ) ^ γ) +
        b * (∑ r : DivisorTuple P k, tupleMass r) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [sum_tupleMass_mul_rpow, sum_tupleMass]
end LongGapsBetweenPrimes
