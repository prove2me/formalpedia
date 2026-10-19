-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:03:08.965056+00:00
-- url     : https://prove2.me/submissions/298edf24-273a-4bf1-bda5-60824b9a2faf

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_factorial_base
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_factorial_succ

open scoped BigOperators

theorem solution (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal =
      1 / (Nat.factorial n : ℝ) := by
  induction n with
  | zero =>
      simpa using
        OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial_base
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial_succ, ih]
      rw [Nat.factorial_succ]
      push_cast
      field_simp <;> ring
