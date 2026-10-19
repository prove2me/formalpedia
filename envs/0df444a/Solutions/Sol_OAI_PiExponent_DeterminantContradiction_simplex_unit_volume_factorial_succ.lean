-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:21:35.368037+00:00
-- url     : https://prove2.me/submissions/1979389d-6a90-4dad-b05c-63349b74f66a

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_volume_eq_inv_factorial

open scoped BigOperators

theorem solution (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      (MeasureTheory.volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal / (n + 1 : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_eq_inv_factorial,
    OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_eq_inv_factorial]
  have hfac : (Nat.factorial (n + 1) : ℝ) = (n + 1 : ℝ) * Nat.factorial n := by
    rw [Nat.factorial_succ]
    push_cast
    rfl
  rw [hfac]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hfn : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hn, hfn]
  <;> ring