-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:11:52.314957+00:00
-- url     : https://prove2.me/submissions/a134ac66-cde7-4d45-9b99-66bcd7cdebfa

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_volume_factorial_formula

open scoped BigOperators Topology

theorem solution
    (m : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ (1 : ℝ)}) =
      ENNReal.toReal (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)}) / (m + 1 : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_factorial_formula (m + 1),
    OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_factorial_formula m]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
