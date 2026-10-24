-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_slice
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:52:45.316288+00:00
-- url     : https://prove2.me/submissions/272dbb9a-9e76-425b-9a75-dca8d816071b

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_slice_fubini
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_slice_eval

open scoped BigOperators

theorem solution
    (n : Nat) (T : Real) (hT : 0 < T)
    (ih : ∀ s : Real, 0 < s →
      MeasureTheory.volume
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < s} =
        ENNReal.ofReal (s ^ n / (n.factorial : Real))) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      (∫⁻ t in Set.Ioo (0 : Real) T,
        ENNReal.ofReal ((T - t) ^ n / (n.factorial : Real))
          ∂MeasureTheory.volume) := by
  rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slice_fubini
    n T hT]
  exact OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slice_eval
    n T hT ih
