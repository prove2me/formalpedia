-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:34:19.836294+00:00
-- url     : https://prove2.me/submissions/579710dd-18c7-4ddd-9251-3bbdba5dd84a

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_unit_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_unit_volume_succ

open scoped BigOperators Topology

theorem solution
    (m : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)}) =
      1 / (Nat.factorial m : ℝ) := by
  induction m with
  | zero =>
      simpa using OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume_zero
  | succ m ih =>
      rw [OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume_succ, ih]
      simp [Nat.factorial_succ]
      field_simp
