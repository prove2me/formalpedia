-- Prove2me | solution 1 for MasulloRepair.common_matrix_coefficient_sum_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T21:12:09.023377+00:00
-- url     : https://prove2.me/submissions/64336984-da52-4178-8c47-c433e1b29335

import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

lemma common_matrix_coefficient_sum_norm_lower_hinner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℕ → H →L[ℂ] H) (a b : H) (n : ℕ) :
    (∑ i ∈ Finset.range n, inner ℂ a (K i b)) =
      inner ℂ a ((∑ i ∈ Finset.range n, K i) b) := by
  simp [ContinuousLinearMap.sum_apply, inner_add_right]

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℕ → H →L[ℂ] H) (a b : H) (c : ℝ) (n : ℕ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hcoef : ∀ i : ℕ, c ≤ (inner ℂ a (K i b)).re) :
    c * n ≤ ‖∑ i ∈ Finset.range n, K i‖ := by
  let S : H →L[ℂ] H := ∑ i ∈ Finset.range n, K i
  have hsum : c * n ≤ ∑ i ∈ Finset.range n, (inner ℂ a (K i b)).re := by
    calc
      c * n = ∑ i ∈ Finset.range n, c := by
        simp [Finset.sum_const, Finset.card_range]
        ring
      _ ≤ ∑ i ∈ Finset.range n, (inner ℂ a (K i b)).re := by
        apply Finset.sum_le_sum
        intro i hi
        exact hcoef i
  have hinner : (∑ i ∈ Finset.range n, inner ℂ a (K i b)) = inner ℂ a (S b) := by
    exact common_matrix_coefficient_sum_norm_lower_hinner K a b n
  have hreal : (∑ i ∈ Finset.range n, (inner ℂ a (K i b)).re) =
      (inner ℂ a (S b)).re := by
    rw [← hinner]
    simp
  calc
    c * n ≤ ∑ i ∈ Finset.range n, (inner ℂ a (K i b)).re := hsum
    _ = (inner ℂ a (S b)).re := hreal
    _ ≤ ‖inner ℂ a (S b)‖ := Complex.re_le_norm _
    _ ≤ ‖a‖ * ‖S b‖ := norm_inner_le_norm _ _
    _ ≤ ‖S‖ := by
      calc
        ‖a‖ * ‖S b‖ ≤ 1 * ‖S b‖ := by
          exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ = ‖S b‖ := one_mul _
        _ ≤ ‖S‖ * ‖b‖ := ContinuousLinearMap.le_opNorm S b
        _ ≤ ‖S‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = ‖S‖ := mul_one _
