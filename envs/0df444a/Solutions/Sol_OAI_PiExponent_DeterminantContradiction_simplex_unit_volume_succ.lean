-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:10:41.339403+00:00
-- url     : https://prove2.me/submissions/c4513e1e-a817-4c29-b83d-1e50187000be

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_factorial

open scoped BigOperators

theorem solution (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      (MeasureTheory.volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal / ((n + 1 : ℕ) : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial,
    OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial,
    Nat.factorial_succ]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hn, hf]
  push_cast
  ring