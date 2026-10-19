-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_succ_slice
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:40:41.067734+00:00
-- url     : https://prove2.me/submissions/02dd7da8-61ca-4cc1-afda-b631760a8bc4

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume_formula
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_slice_integral_formula

open scoped BigOperators

theorem solution
    (m : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ |
        (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ U}).toReal =
      ∫ t in (0 : ℝ)..U,
        (MeasureTheory.volume
          {x : Fin m → ℝ |
            (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U - t}).toReal := by
  rw [OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_formula
    (m + 1) U hU]
  exact (OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_slice_integral_formula
    m U hU).symm
