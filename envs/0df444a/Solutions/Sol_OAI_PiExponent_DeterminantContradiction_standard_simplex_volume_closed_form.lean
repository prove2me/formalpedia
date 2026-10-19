-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:12:32.62423+00:00
-- url     : https://prove2.me/submissions/771271d7-29be-4935-b5ae-f31742868db8

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplexVolume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplexVolume_succ

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) =
      1 / ((Nat.factorial n : ℕ) : ℝ) := by
  induction n with
  | zero =>
      have h := OAI.PiExponent.DeterminantContradiction.standardSimplexVolume_zero
      simpa using h
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.standardSimplexVolume_succ n, ih,
        Nat.factorial_succ]
      push_cast
      field_simp
      <;> ring