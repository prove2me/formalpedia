-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_succ_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:09.777588+00:00
-- url     : https://prove2.me/submissions/99722e8b-c574-4f27-8852-1d358b879bc2

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_step
open scoped BigOperators

theorem solution (n : Nat)
    (h : MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_step <;> assumption
