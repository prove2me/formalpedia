-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:59:37.802066+00:00
-- url     : https://prove2.me/submissions/225a1c1f-ad2b-48ab-887f-5a3ec638b5ba

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_slice
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
  apply OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice <;> assumption
