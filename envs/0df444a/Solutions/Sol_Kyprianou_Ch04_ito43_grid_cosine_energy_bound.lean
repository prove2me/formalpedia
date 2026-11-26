-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_grid_cosine_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:10:48.710134+00:00
-- url     : https://prove2.me/submissions/edfc10a4-4623-4c9b-b083-c1d9bdc9155b

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

/-- On paths with increments in a fixed compact interval, cosine deficits dominate squared increments. -/
theorem solution (n : ℕ) (D : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hD : ∀ k < n, |D k| ≤ R) :
    (∑ k ∈ Finset.range n, (D k)^2) ≤
      (Real.pi ^ 2 * R^2 / 2) *
        ∑ k ∈ Finset.range n, (1 - Real.cos (D k/R)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have h : |D k/R| ≤ Real.pi := by
    rw [abs_div,abs_of_pos hR]
    exact ((div_le_one hR).mpr (hD k (Finset.mem_range.mp hk))).trans
      (by linarith [Real.pi_gt_three])
  have hc := Real.cos_le_one_sub_mul_cos_sq h
  have hp : 0 < Real.pi^2 * R^2 / 2 := by positivity
  have H := mul_le_mul_of_nonneg_left (show 2/Real.pi^2*(D k/R)^2 ≤ 1-Real.cos (D k/R) by linarith)
    hp.le
  calc
    (D k)^2 = (Real.pi^2*R^2/2)*(2/Real.pi^2*(D k/R)^2) := by
      field_simp [hR.ne',Real.pi_ne_zero]
    _ ≤ _ := H
