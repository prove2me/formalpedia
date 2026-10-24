-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:38:57.158993+00:00
-- url     : https://prove2.me/submissions/108d7be7-78aa-4bea-ab56-6644144397f4

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_unit
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.simplexVolume_unit <;> assumption
