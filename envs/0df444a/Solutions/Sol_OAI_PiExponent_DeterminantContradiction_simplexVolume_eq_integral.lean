-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:27:01.911456+00:00
-- url     : https://prove2.me/submissions/f402bc33-4366-45b1-90fb-b8210877ddce

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_factorial
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_intervalIntegral_one_sub_pow
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_volume_factorial (n + 1),
    OAI.PiExponent.DeterminantContradiction.simplex_volume_factorial n,
    OAI.PiExponent.DeterminantContradiction.intervalIntegral_one_sub_pow n]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / (Nat.factorial n : Real)))]
  apply congrArg ENNReal.ofReal
  rw [Nat.factorial_succ]
  push_cast
  field_simp <;> positivity
