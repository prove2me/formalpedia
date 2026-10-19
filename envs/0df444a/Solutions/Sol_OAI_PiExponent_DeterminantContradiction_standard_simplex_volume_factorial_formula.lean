-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_factorial_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:16:18.622433+00:00
-- url     : https://prove2.me/submissions/aa53afe7-dd38-46f1-ac35-64802b9d7b37

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_volume_succ

open scoped BigOperators Topology

theorem solution
    (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) =
      1 / (Nat.factorial n : ℝ) := by
  induction n with
  | zero =>
      simpa using
        OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_zero
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_succ, ih]
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      <;> ring