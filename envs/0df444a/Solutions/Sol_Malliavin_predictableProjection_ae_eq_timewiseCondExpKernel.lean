-- Prove2me | solution 1 for Malliavin.predictableProjection_ae_eq_timewiseCondExpKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:03.829659+00:00
-- url     : https://prove2.me/submissions/dbc38cc4-f36a-4fe7-9132-87898a256887

import Definitions.Def_Malliavin_NaturalItoDuality
import Mathlib.Probability.Kernel.Condexp
import Definitions.Def_Malliavin_TimewiseCondExp
import Theorems.Thm_Malliavin_memLp_timewiseCondExpKernelRepresentative
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
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P]
        timewiseCondExpKernelRepresentative 𝓕 U := by
  have hL2 := memLp_timewiseCondExpKernelRepresentative 𝓕 U hpred
  let V : PredictableProcessL2 𝓕 P :=
    ⟨hL2.toLp (timewiseCondExpKernelRepresentative 𝓕 U),
      hpred.congr hL2.coeFn_toLp.symm⟩
  have hV : ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      (fun w ↦ (V : ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
        fun w ↦ ∫ w', U (t, w') ∂condExpKernel P (𝓕 t) w := by
    filter_upwards [Measure.ae_ae_of_ae_prod hL2.coeFn_toLp] with t ht
    filter_upwards [ht] with w hw
    simpa only [V, timewiseCondExpKernelRepresentative] using hw
  rw [predictableProjection_eq_of_ae_timewiseCondExpKernel 𝓕 U V hV]
  exact hL2.coeFn_toLp
end Malliavin
