-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unit_simplex_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:18:49.370304+00:00
-- url     : https://prove2.me/submissions/cdae186d-375f-43c6-bbb5-0595c66b63f4

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_volume_succ
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_volume_zero

open scoped BigOperators

theorem solution (k : ℕ) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal =
      (Nat.factorial k : ℝ)⁻¹ := by
  induction k with
  | zero =>
      simpa using OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_zero
  | succ k ih =>
      rw [OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_succ, ih]
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp