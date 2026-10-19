-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T13:23:37.646624+00:00
-- url     : https://prove2.me/submissions/6d8085ee-9d69-44f4-897b-d9b76ef52568

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_scale
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_volume

open scoped BigOperators

theorem solution (k : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U}).toReal =
      (U ^ k) / (Nat.factorial k : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_scale
    (k := k) (U := U) (hU := hU),
    OAI.PiExponent.DeterminantContradiction.unit_simplex_volume]
  simp [div_eq_mul_inv, mul_comm]