-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_integral_reduce
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:49:16.352177+00:00
-- url     : https://prove2.me/submissions/600980b0-f223-4a87-9b34-45f433154f63

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
      (∫⁻ t in Set.Icc (0 : Real) r,
        ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))
        ∂MeasureTheory.volume) := by
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  exact ih (r - t) (sub_nonneg.mpr ht.2)