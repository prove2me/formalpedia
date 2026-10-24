-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:12.8482+00:00
-- url     : https://prove2.me/submissions/3c578e19-a72a-4e09-b80c-72328b0bed8f

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero_v2
open scoped BigOperators

theorem solution :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_v2 <;> assumption
