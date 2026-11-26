-- Prove2me | solution 1 for Malliavin.memLp_timewiseCondExpKernelRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:42:05.599455+00:00
-- url     : https://prove2.me/submissions/b62c8e13-5ca1-40ed-84d7-b92faeffba74

import Definitions.Def_Malliavin_NaturalItoDuality
import Mathlib.Probability.Kernel.Condexp
import Definitions.Def_Malliavin_TimewiseCondExp
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_memLp_timeSection_ae
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P)
    (hpred : AEStronglyMeasurable[𝓕.predictable]
      (timewiseCondExpKernelRepresentative 𝓕 U)
      (nonnegativeLebesgueMeasure.prod P)) :
    MemLp (timewiseCondExpKernelRepresentative 𝓕 U) 2
      (nonnegativeLebesgueMeasure.prod P) := by
  let C := timewiseCondExpKernelRepresentative 𝓕 U
  have hCmeas : AEStronglyMeasurable C
      (nonnegativeLebesgueMeasure.prod P) :=
    hpred.mono (predictable_le_prod 𝓕)
  apply (memLp_two_iff_integrable_sq hCmeas).2
  have hCsqMeas : AEStronglyMeasurable (fun z ↦ C z ^ 2)
      (nonnegativeLebesgueMeasure.prod P) := hCmeas.pow 2
  apply (integrable_prod_iff hCsqMeas).2
  constructor
  · filter_upwards [memLp_timeSection_ae U] with t hUt
    have hCE : (fun w ↦ C (t, w)) =ᵐ[P]
        P[(fun w ↦ U (t, w)) | 𝓕 t] := by
      exact (condExp_ae_eq_integral_condExpKernel (𝓕.le t)
        (hUt.integrable one_le_two)).symm
    exact ((memLp_congr_ae hCE).2 (hUt.condExp one_le_two)).integrable_sq
  · have hUOuter : Integrable
        (fun t ↦ ∫ w, ‖(U (t, w)) ^ 2‖ ∂P)
        nonnegativeLebesgueMeasure :=
      (Lp.memLp U).integrable_sq.integral_norm_prod_left
    have hCOuterMeas : AEStronglyMeasurable
        (fun t ↦ ∫ w, ‖C (t, w) ^ 2‖ ∂P)
        nonnegativeLebesgueMeasure := hCsqMeas.norm.integral_prod_right'
    apply hUOuter.mono' hCOuterMeas
    filter_upwards [memLp_timeSection_ae U] with t hUt
    have hCE : (fun w ↦ C (t, w)) =ᵐ[P]
        P[(fun w ↦ U (t, w)) | 𝓕 t] := by
      exact (condExp_ae_eq_integral_condExpKernel (𝓕.le t)
        (hUt.integrable one_le_two)).symm
    have hEq : (∫ w, ‖C (t, w) ^ 2‖ ∂P) =
        ∫ w, ‖P[(fun w ↦ U (t, w)) | 𝓕 t] w‖ ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hCE] with w hw
      rw [hw, norm_pow]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), hEq]
    have hUnormSq : Integrable (fun w ↦ ‖U (t, w)‖ ^ 2) P := by
      simpa only [norm_pow] using hUt.integrable_sq.norm
    simpa only [Real.rpow_two, norm_pow] using
      integral_norm_condExp_rpow_le (m := 𝓕 t) (p := (2 : ℝ)) one_le_two
        (by simpa only [Real.rpow_two] using hUnormSq)
end Malliavin
