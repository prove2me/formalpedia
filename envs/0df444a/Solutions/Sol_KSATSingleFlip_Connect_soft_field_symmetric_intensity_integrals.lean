-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_symmetric_intensity_integrals
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:28.537074+00:00
-- url     : https://prove2.me/submissions/a0f5b351-2328-4e57-9b8f-a370dda4cc0b

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_potential_intensity_identity
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_intensity_bound
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_potential_bounds
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect

theorem solution (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hsym : Measure.map (fun z : ℝ => -z) ν = ν)
    (hcosh : Integrable Real.cosh ν) :
    Integrable wInt ν ∧ Integrable Real.exp ν ∧
    (∫ z, wInt z ∂ν) = (∫ z, Real.cosh z ∂ν) + hPot ν/2 ∧
    (∫ z, Real.exp z ∂ν) = ∫ z, Real.cosh z ∂ν := by
  have hwc : Continuous wInt := by unfold wInt; fun_prop
  have hwi : Integrable wInt ν := by
    apply (hcosh.const_mul 2).mono' hwc.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold wInt; positivity)]
    exact soft_field_intensity_bound z
  have hwni : Integrable (fun z => wInt (-z)) ν := by
    have hmeas : Continuous (fun z => wInt (-z)) := hwc.comp continuous_neg
    apply (hcosh.const_mul 2).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold wInt; positivity)]
    simpa only [Real.cosh_neg] using soft_field_intensity_bound (-z)
  have hexpi : Integrable Real.exp ν := by
    apply (hcosh.const_mul 2).mono' Real.continuous_exp.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z), Real.cosh_eq]
    have := Real.exp_pos (-z)
    linarith
  have hnegexpi : Integrable (fun z => Real.exp (-z)) ν := by
    have hmeas : Continuous (fun z => Real.exp (-z)) := Real.continuous_exp.comp continuous_neg
    apply (hcosh.const_mul 2).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-z)), Real.cosh_eq]
    have := Real.exp_pos z
    linarith
  have hwsym : (∫ z, wInt (-z) ∂ν) = ∫ z, wInt z ∂ν := by
    have hh := integral_map (show AEMeasurable (fun z : ℝ => -z) ν by fun_prop) hwc.aestronglyMeasurable
    rw [hsym] at hh
    exact hh.symm
  have hesym : (∫ z, Real.exp (-z) ∂ν) = ∫ z, Real.exp z ∂ν := by
    have hh := integral_map (show AEMeasurable (fun z : ℝ => -z) ν by fun_prop) Real.continuous_exp.aestronglyMeasurable
    rw [hsym] at hh
    exact hh.symm
  refine ⟨hwi,hexpi,?_,?_⟩
  · have hEq : hPot ν = ∫ z, (wInt z+wInt (-z)-2*Real.cosh z) ∂ν := by
      unfold hPot pairing
      apply integral_congr_ae
      exact Filter.Eventually.of_forall soft_field_potential_intensity_identity
    have hsub := integral_sub (hwi.add hwni) (hcosh.const_mul 2)
    change (∫ z, wInt z+wInt (-z)-2*Real.cosh z ∂ν) = _ at hsub
    rw [hsub] at hEq
    change hPot ν = (∫ z, wInt z+wInt (-z) ∂ν) - (∫ z, 2*Real.cosh z ∂ν) at hEq
    rw [integral_add hwi hwni, integral_const_mul, hwsym] at hEq
    linarith
  · have hEq : (∫ z, Real.cosh z ∂ν) = (∫ z, (Real.exp z+Real.exp (-z))/2 ∂ν) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall Real.cosh_eq
    rw [integral_div, integral_add hexpi hnegexpi, hesym] at hEq
    linarith
