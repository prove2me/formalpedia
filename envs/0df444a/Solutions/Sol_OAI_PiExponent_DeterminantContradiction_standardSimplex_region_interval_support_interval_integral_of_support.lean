-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.interval_integral_of_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:10.289783+00:00
-- url     : https://prove2.me/submissions/2295a6e4-c5a5-4ec3-aee5-93f4aa34931a

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib

open MeasureTheory Filter Topology in

theorem solution {H : Real} (hH : 0 < H) (f g : Real → Real) (hout : ∀ t, t < 0 ∨ H < t → f t = 0) (hmid : ∀ t, 0 < t → t < H → f t = g t) :
    (∫ t : Real, f t) = ∫ t in (0 : Real)..H, g t := by
  have h1 : (∫ t : Real, f t) = ∫ t in Set.Icc 0 H, f t := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro t ht
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    exact hout t ht
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hH.le]
  refine intervalIntegral.integral_congr_ae ?_
  have : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ≠ H := by
    have h := (MeasureTheory.compl_mem_ae_iff (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (s := {H})).mpr (MeasureTheory.measure_singleton H)
    filter_upwards [h] with t ht using ht
  filter_upwards [this] with t htH ht
  rw [Set.uIoc_of_le hH.le] at ht
  exact hmid t ht.1 (lt_of_le_of_ne ht.2 htH)
