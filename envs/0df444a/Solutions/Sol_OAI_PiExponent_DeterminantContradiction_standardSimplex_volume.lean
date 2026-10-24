-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:35:09.922875+00:00
-- url     : https://prove2.me/submissions/6ec029f7-51e3-4fbd-9a0a-02e942fb8c06

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_slicing
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_factorial_succ
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      ENNReal.ofReal (1 / (n.factorial : Real)) := by
  induction n with
  | zero =>
      exact OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_zero
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slicing, ih]
      exact OAI.PiExponent.DeterminantContradiction.standardSimplex_factorial_succ n