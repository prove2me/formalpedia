-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:53:08.342646+00:00
-- url     : https://prove2.me/submissions/eeb7b95e-14cc-4630-9e04-782642885629

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_eq_inv_factorial

open scoped BigOperators

theorem solution (m : ℕ) :
    (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ 1}).toReal =
      ((MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1}).toReal) / (m + 1 : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_eq_inv_factorial,
    OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_eq_inv_factorial]
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial m : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring