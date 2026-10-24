-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:37:06.856527+00:00
-- url     : https://prove2.me/submissions/ea2563f4-cbfe-4d46-8f41-c29bafcb9ef3

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real) (V : ENNReal) :
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then
        ENNReal.ofReal (((T - t) / T) ^ m) * V
      else 0) =
      (MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m)
        else 0)) * V := by
  let f : Real → ENNReal := fun t =>
    if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m) else 0
  have hs : MeasurableSet {t : Real | 0 ≤ t ∧ t < T} := by
    exact measurableSet_Ici.inter measurableSet_Iio
  have hg : Measurable (fun t : Real => ENNReal.ofReal (((T - t) / T) ^ m)) := by
    fun_prop
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite hs hg measurable_const
  calc
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then
          ENNReal.ofReal (((T - t) / T) ^ m) * V
        else 0) =
        MeasureTheory.lintegral MeasureTheory.volume (fun t : Real => f t * V) := by
          apply MeasureTheory.lintegral_congr
          intro t
          by_cases h : 0 ≤ t ∧ t < T <;> simp [f, h]
    _ = (MeasureTheory.lintegral MeasureTheory.volume f) * V :=
          MeasureTheory.lintegral_mul_const V hf
    _ = (MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
          if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m)
          else 0)) * V := by rfl