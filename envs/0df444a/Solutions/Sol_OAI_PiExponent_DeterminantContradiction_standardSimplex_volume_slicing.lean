-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slicing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:04:46.846991+00:00
-- url     : https://prove2.me/submissions/50f4be7f-48e0-45f9-b480-d9e8f5e73a74

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_slicing_constant
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_integral_evaluation

open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {y : Fin (n + 1) → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      MeasureTheory.volume
        {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} / (n + 1 : ENNReal) := by
  rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_slicing_constant n]
  exact OAI.PiExponent.DeterminantContradiction.standardSimplex_integral_evaluation n
    (MeasureTheory.volume
      {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1})