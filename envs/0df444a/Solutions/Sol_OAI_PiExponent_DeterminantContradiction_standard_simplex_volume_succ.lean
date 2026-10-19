-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:04:07.477219+00:00
-- url     : https://prove2.me/submissions/9cf6a72c-afb1-4de1-a7dc-e4c0e05aff6e

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_volume_closed_form

open scoped BigOperators Topology

theorem solution
    (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ENNReal.toReal (MeasureTheory.volume
          {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by
  rw [OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_closed_form,
    OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_closed_form]
  rw [Nat.factorial_succ]
  push_cast
  field_simp [Nat.factorial_ne_zero]