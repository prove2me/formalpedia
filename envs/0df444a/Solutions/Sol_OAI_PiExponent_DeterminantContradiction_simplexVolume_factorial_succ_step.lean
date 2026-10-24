-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_succ_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:12:54.725168+00:00
-- url     : https://prove2.me/submissions/9e5b80b5-d0a0-4281-82e6-844f2902624b

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_recurrence
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_factorial_ennreal_step
open scoped BigOperators

theorem solution (n : Nat)
    (h : MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence n,
    h,
    OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_ennreal_step n]