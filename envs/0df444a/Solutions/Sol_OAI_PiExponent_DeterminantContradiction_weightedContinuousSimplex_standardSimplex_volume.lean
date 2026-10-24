-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:49:34.632406+00:00
-- url     : https://prove2.me/submissions/f90ffbeb-57b0-4701-a408-5d2fa46cf88e

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_standardSimplex_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_standardSimplex_volume_slice
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_standardSimplex_volume_integral
open scoped BigOperators

theorem solution
    (n : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T}
      = ENNReal.ofReal (T ^ n / (n.factorial : Real)) := by
  induction n generalizing T with
  | zero =>
      exact OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_zero T hT
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_slice
        n T hT (fun s hs => ih s hs)]
      exact OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_integral
        n T hT