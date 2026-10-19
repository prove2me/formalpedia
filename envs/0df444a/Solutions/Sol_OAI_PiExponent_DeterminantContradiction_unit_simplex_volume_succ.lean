-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:29:44.425581+00:00
-- url     : https://prove2.me/submissions/bf029232-6855-4721-8230-0b1a5c73aa8b

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_volume_eq_inv_factorial

open scoped BigOperators

theorem solution (k : ℕ) :
    (MeasureTheory.volume
      {x : Fin (k + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (k + 1), x i ≤ 1}).toReal =
      ((MeasureTheory.volume
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal) /
        ((k + 1 : ℕ) : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_eq_inv_factorial (k + 1),
    OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_eq_inv_factorial k]
  simp only [Nat.factorial_succ]
  push_cast
  have hk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hk, hk1]