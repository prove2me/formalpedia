-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:19:48.268987+00:00
-- url     : https://prove2.me/submissions/f1b5ff2b-e3a1-4cf5-aa3a-a89e55a296f0

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_integral
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_integral
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_integral,
    OAI.PiExponent.DeterminantContradiction.unit_simplex_integral]