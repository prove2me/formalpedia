-- Prove2me | solution 1 for Kyprianou.Ch02.measurableRealBochnerIntegralOnMeasuresV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:37:38.323908+00:00
-- url     : https://prove2.me/submissions/60ae3942-ef63-4259-afe0-d55d24dabda3

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (fun μ : Measure ℝ => ∫ x, f x ∂μ) := by
  classical
  let J (μ : Measure ℝ) := ∫⁻ x, ENNReal.ofReal |f x| ∂μ
  let U (μ : Measure ℝ) := (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal
  let V (μ : Measure ℝ) := (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal
  have hJ : Measurable J :=
    Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.abs)
  have hU : Measurable U := ENNReal.measurable_toReal.comp
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf))
  have hV : Measurable V := ENNReal.measurable_toReal.comp
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.neg))
  have hEq : (fun μ : Measure ℝ => ∫ x, f x ∂μ) =
      fun μ => if J μ < ⊤ then U μ - V μ else 0 := by
    funext μ
    have hInt : Integrable f μ ↔ J μ < ⊤ := by
      simp only [Integrable, hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal_abs]
      exact and_iff_right hf.aestronglyMeasurable
    split_ifs with hj
    · exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hInt.mpr hj)
    · exact integral_undef (mt hInt.mp hj)
  rw [hEq]
  exact Measurable.ite (measurableSet_lt hJ measurable_const) (hU.sub hV) measurable_const
