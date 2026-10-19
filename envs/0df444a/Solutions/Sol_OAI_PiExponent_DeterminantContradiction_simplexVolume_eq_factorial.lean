-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:37:58.063096+00:00
-- url     : https://prove2.me/submissions/18c9ae91-b67c-44ca-8df9-b3ee411ce6b2

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) =
    (Nat.factorial n : ℝ)⁻¹ := by
  induction n with
  | zero =>
      simpa using
        OAI.PiExponent.DeterminantContradiction.simplexVolume_zero
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_succ, ih]
      simp only [Nat.factorial_succ, Nat.cast_mul]
      have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
        positivity
      field_simp [hfac, hn]