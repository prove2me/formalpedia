-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_jump_moments
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:28.715587+00:00
-- url     : https://prove2.me/submissions/4270d591-72da-4780-8abf-30c1a499bdad

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_tilt_identities
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_symmetric_intensity_integrals
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hsym : Measure.map (fun z : ℝ => -z) ν = ν)
    (hcosh : Integrable Real.cosh ν) :
    let μ := Measure.map aShift (ν.withDensity fun z => ENNReal.ofReal (wInt z))
    let u := ∫ z, Real.cosh z ∂ν
    μ Set.univ = ENNReal.ofReal (u+hPot ν/2) ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) = ENNReal.ofReal (2*u) ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ) = ENNReal.ofReal u := by
  dsimp only
  let μ := Measure.map aShift (ν.withDensity fun z => ENNReal.ofReal (wInt z))
  let u := ∫ z, Real.cosh z ∂ν
  obtain ⟨hwi,hexpi,hwmean,hexpmean⟩ := soft_field_symmetric_intensity_integrals ν hsym hcosh
  have hw : Measurable (fun z => ENNReal.ofReal (wInt z)) := by unfold wInt; fun_prop
  have ha : Measurable aShift := by unfold aShift; fun_prop
  have hw0 (z : ℝ) : 0 ≤ wInt z := by unfold wInt; positivity
  have hA : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp x)) := by fun_prop
  have hB : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-x))) := by fun_prop
  have hA' : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (aShift z))) := hA.comp ha
  have hB' : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (-aShift z))) := hB.comp ha
  have hwlin : (∫⁻ z, ENNReal.ofReal (wInt z) ∂ν) = ENNReal.ofReal (∫ z, wInt z ∂ν) := by
    exact (ofReal_integral_eq_lintegral_ofReal hwi (Filter.Eventually.of_forall hw0)).symm
  refine ⟨?_,?_,?_⟩
  · change μ Set.univ = _
    dsimp [μ]
    rw [Measure.map_apply ha MeasurableSet.univ]
    simp only [Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [hwlin,hwmean]
  · change (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) = _
    dsimp [μ]
    rw [lintegral_map hA ha, lintegral_withDensity_eq_lintegral_mul ν hw hA']
    have heq : (fun z : ℝ => (ENNReal.ofReal (wInt z) * ENNReal.ofReal (Real.exp (aShift z)))) =
        fun z => ENNReal.ofReal (2*Real.cosh z) := by
      funext z
      rw [← ENNReal.ofReal_mul (hw0 z), (soft_field_tilt_identities z).1]
    change (∫⁻ z, ENNReal.ofReal (wInt z)*ENNReal.ofReal (Real.exp (aShift z)) ∂ν) = _
    rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal (hcosh.const_mul 2) (Filter.Eventually.of_forall (fun z => by positivity)), integral_const_mul]
  · change (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ) = _
    dsimp [μ]
    rw [lintegral_map hB ha, lintegral_withDensity_eq_lintegral_mul ν hw hB']
    have heq : (fun z : ℝ => ENNReal.ofReal (wInt z) * ENNReal.ofReal (Real.exp (-aShift z))) =
        fun z => ENNReal.ofReal (Real.exp z) := by
      funext z
      rw [← ENNReal.ofReal_mul (hw0 z), (soft_field_tilt_identities z).2]
    change (∫⁻ z, ENNReal.ofReal (wInt z)*ENNReal.ofReal (Real.exp (-aShift z)) ∂ν) = _
    rw [heq, ← ofReal_integral_eq_lintegral_ofReal hexpi (Filter.Eventually.of_forall (fun z => le_of_lt (Real.exp_pos z))), hexpmean]
