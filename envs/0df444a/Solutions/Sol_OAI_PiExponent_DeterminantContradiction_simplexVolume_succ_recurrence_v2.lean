-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:59:55.992554+00:00
-- url     : https://prove2.me/submissions/02a5b58a-a551-4949-a207-8631641e5ef4

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_factorial
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexFactorial_recurrence
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (n + 1 : Real)) *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial,
    OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial]
  exact (OAI.PiExponent.DeterminantContradiction.simplexFactorial_recurrence n).symm