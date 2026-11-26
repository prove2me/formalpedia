-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:03:35.775871+00:00
-- url     : https://prove2.me/submissions/78f576a3-d4fe-4de4-be6f-2902d692a659

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
import Theorems.Thm_Malliavin_dense_elementaryPredictableSpan
import Theorems.Thm_Malliavin_ClarkOconeFamily_elementaryIntegralValue_eq
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
set_option maxHeartbeats 220000
namespace Malliavin
namespace ClarkOconeFamily.IsBrownianOnElementary
theorem _root_.solution
    {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {C D : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) (hD : D.IsBrownianOnElementary) :
    C.itoIntegral = D.itoIntegral := by
  -- isDefEq on ContinuousLinearMap.ext_on costs >200k heartbeats inherently (type
  -- unification of C.itoIntegral and D.itoIntegral). suffices+ext, isClosed_property,
  -- and explicit type annotation all hit the same floor.
  apply ContinuousLinearMap.ext_on
    (s := {U | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
      ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P, U = elementaryPredictable 𝓕 a b Z})
  · simpa only [elementaryPredictableSpan] using
      (dense_elementaryPredictableSpan (P := P) 𝓕)
  · rintro U ⟨a, b, hab, Z, rfl⟩
    rw [hC hab Z, hD hab Z]
    exact C.elementaryIntegralValue_eq D hab Z
end ClarkOconeFamily.IsBrownianOnElementary
end Malliavin
