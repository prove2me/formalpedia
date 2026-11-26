-- Prove2me | solution 1 for Malliavin.smoothNaturalItoDuality_of_elementary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:08.435546+00:00
-- url     : https://prove2.me/submissions/a149f76e-6c79-446b-9070-07b5d7aa75b6

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
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
import Theorems.Thm_Malliavin_dense_elementaryPredictableSpan
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_naturalItoIntegral_elementaryPredictable
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


attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hElementary : SmoothElementaryNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat := by
  intro G hG U
  let V := predictableProjection 𝓅
    (Malliavin.timeDerivative hB coordinate coordinate_apply generated
      (hG.mderivLp P))
  let L : PredictableProcessL2 𝓅 P →L[ℝ] ℝ :=
    (innerSL ℝ (hG.toLp P - expectationL2 (hG.toLp P))).comp
      (naturalItoIntegral hB hsm hnat)
  let R : PredictableProcessL2 𝓅 P →L[ℝ] ℝ := innerSL ℝ V
  have hLR : L = R := by
    apply ContinuousLinearMap.ext_on
      (s := {X | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
        ∃ Z : lpMeas ℝ ℝ (𝓅 a) 2 P, X = elementaryPredictable 𝓅 a b Z})
    · simpa only [elementaryPredictableSpan] using
        (dense_elementaryPredictableSpan (P := P) 𝓅)
    · rintro X ⟨a, b, hab, Z, rfl⟩
      change inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
          (naturalItoIntegral hB hsm hnat (elementaryPredictable 𝓅 a b Z)) =
        inner ℝ V (elementaryPredictable 𝓅 a b Z)
      rw [naturalItoIntegral_elementaryPredictable hB hsm hnat hab Z]
      exact hElementary G hG a b hab Z
  have happ := congrArg
    (fun T : PredictableProcessL2 𝓅 P →L[ℝ] ℝ ↦ T U) hLR
  exact happ
end Malliavin
