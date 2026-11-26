-- Prove2me | solution 1 for Kyprianou.Ch04.affineStepsBoundedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:46:58.460292+00:00
-- url     : https://prove2.me/submissions/e3d1a85c-d40a-40b3-8bcb-94da49e2cbe1

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- A finite sum of affine and step paths is bounded on a compact interval. -/
theorem solution {ι : Type} (s : Finset ι) (a r : ι → ℝ)
    (b : ℝ) (T : NNReal) (U : NNReal → ℝ)
    (hU : ∀ t ≤ T, U t = b * (t : ℝ) +
      ∑ i ∈ s, if r i ≤ (t : ℝ) then a i else 0) :
    ∀ t ≤ T, |U t| ≤ |b| * (T : ℝ) + ∑ i ∈ s, |a i| := by
  intro t ht
  rw [hU t ht]
  calc
    _ ≤ |b * (t : ℝ)| + |∑ i ∈ s, if r i ≤ (t : ℝ) then a i else 0| := abs_add_le _ _
    _ ≤ |b| * (T : ℝ) + ∑ i ∈ s, |a i| := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg t.coe_nonneg]
        exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) (abs_nonneg b)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        split_ifs
        · exact le_rfl
        · simpa using abs_nonneg (a i)
