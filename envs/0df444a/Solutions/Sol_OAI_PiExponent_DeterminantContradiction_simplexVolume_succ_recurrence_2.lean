-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:04.20881+00:00
-- url     : https://prove2.me/submissions/b047f625-bea7-42c7-90c9-f24d49ffe09b

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_slice_recurrence
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice_recurrence <;> assumption
