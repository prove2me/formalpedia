-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq_naturalItoIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:15.326796+00:00
-- url     : https://prove2.me/submissions/138a9f17-8946-45a2-a571-c83691c6f677

import Definitions.Def_Malliavin_ElementaryIto
import Definitions.Def_Malliavin_PredictableDensity
import Definitions.Def_Malliavin_ItoConstruction
import Theorems.Thm_Malliavin_naturalItoIntegral_elementaryPredictable
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_ClarkOconeFamily_elementaryIntegralValue_eq_elementaryBrownianValue
import Theorems.Thm_Malliavin_dense_elementaryPredictableSpan
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.mem_symmetricSubmodule


attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply

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
namespace ClarkOconeFamily.IsBrownianOnElementary
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) :
    C.itoIntegral =
      naturalItoIntegral C.isPreBrownian C.stronglyMeasurable C.naturalFiltration := by
  apply ContinuousLinearMap.ext_on
    (s := {U | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
      ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P, U = elementaryPredictable 𝓕 a b Z})
  · simpa only [elementaryPredictableSpan] using
      (dense_elementaryPredictableSpan (P := P) 𝓕)
  · rintro U ⟨a, b, hab, Z, rfl⟩
    rw [hC hab Z,
      naturalItoIntegral_elementaryPredictable C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration]
    exact C.elementaryIntegralValue_eq_elementaryBrownianValue hab Z
end ClarkOconeFamily.IsBrownianOnElementary
end Malliavin
