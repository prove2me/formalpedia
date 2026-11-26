-- Prove2me | solution 1 for Malliavin.smoothElementaryNaturalItoDuality_of_pastCylinderDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:15.118544+00:00
-- url     : https://prove2.me/submissions/706ae7d0-cc6f-4fa8-b73b-5a5849b7019b

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
import Theorems.Thm_Malliavin_smoothElementaryNaturalItoDuality_pastCylinder
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
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (hdense : PastCylinderDense hB coordinate coordinate_apply hsm hnat) :
    SmoothElementaryNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat := by
  intro G hG a b hab Z
  let V := predictableProjection 𝓕
    (Malliavin.timeDerivative hB coordinate coordinate_apply generated
      (hG.mderivLp P))
  let L : lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] ℝ :=
    (innerSL ℝ (hG.toLp P - expectationL2 (hG.toLp P))).comp
      (elementaryBrownianCoefficientCLM hB hsm hnat hab)
  let R : lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] ℝ :=
    (innerSL ℝ V).comp
      (elementaryPredictableCoefficientCLM (P := P) 𝓕 a b)
  have hLR : L = R := by
    apply ContinuousLinearMap.ext_on
      (s := pastCylinderSet hB coordinate coordinate_apply hsm hnat a)
    · simpa only [pastCylinderSpan] using hdense a
    · rintro X ⟨n, f, hf, hb, hb', t, ht, rfl⟩
      simp only [L, R, V, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
        elementaryBrownianCoefficientCLM_apply,
        elementaryPredictableCoefficientCLM_apply]
      exact smoothElementaryNaturalItoDuality_pastCylinder
        hB coordinate coordinate_apply generated hsm hnat G hG
          f hf hb hb' t a b hab ht
  have happ := congrArg
    (fun T : lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] ℝ ↦ T Z) hLR
  simpa only [L, R, V, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    elementaryBrownianCoefficientCLM_apply,
    elementaryPredictableCoefficientCLM_apply] using happ
end Malliavin
