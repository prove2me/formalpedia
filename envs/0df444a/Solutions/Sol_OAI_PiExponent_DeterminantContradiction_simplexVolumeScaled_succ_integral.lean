-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:44:17.58512+00:00
-- url     : https://prove2.me/submissions/cf776561-8829-4537-bc73-ebb37326c6c8

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_integral_reduce
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_power_integral
open scoped BigOperators

theorem solution
    (n : Nat) (r : Real) (hr : 0 ≤ r)
    (ih : ∀ s : Real, 0 ≤ s →
      MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ s} =
        ENNReal.ofReal (s ^ n / (Nat.factorial n : Real))) :
    (∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume) =
      ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by
  calc
    (∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume) =
      (∫⁻ t in Set.Icc (0 : Real) r,
        ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))
        ∂MeasureTheory.volume) :=
      OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_integral_reduce
        n r hr ih
    _ = ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) :=
      OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_integral
        n r hr