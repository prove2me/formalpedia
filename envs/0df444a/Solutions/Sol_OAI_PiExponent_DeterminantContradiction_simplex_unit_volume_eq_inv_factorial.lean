-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_eq_inv_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:01:37.99604+00:00
-- url     : https://prove2.me/submissions/b16343c6-6f3f-4745-827e-3aadc122b79b

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_base
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_succ

open scoped BigOperators

theorem solution (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal =
      (Nat.factorial n : ℝ)⁻¹ := by
  induction n with
  | zero =>
      simpa using
        OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_base
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_succ n,
        ih, Nat.factorial_succ]
      push_cast
      have hn : (↑(n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hf : (↑(Nat.factorial n) : ℝ) ≠ 0 := by positivity
      field_simp [hn, hf]