-- Prove2me | solution 1 for Malliavin.centeredNaturalItoIntegral_bestNaturalItoIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:22.993146+00:00
-- url     : https://prove2.me/submissions/8f8bfd45-ed86-4d55-b6c6-565eee3724c8

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_naturalItoIntegral_bestNaturalItoIntegrand
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_sub_centeredNaturalItoRangeProjection_mem_orthogonal
import Theorems.Thm_Malliavin_naturalMartingaleRepresentation_iff_centeredNaturalItoRange_orthogonal_eq_bot
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
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
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.mem_symmetricSubmodule


attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredWienerIntegral_coe

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (G : (CameronMartin.expectationMap P).ker) :
    centeredNaturalItoIntegralIsometry hB hsm hnat
      (bestNaturalItoIntegrand hB hsm hnat G) = G := by
  have hres := sub_centeredNaturalItoRangeProjection_mem_orthogonal hB hsm hnat G
  have horth :=
    (naturalMartingaleRepresentation_iff_centeredNaturalItoRange_orthogonal_eq_bot
      hB hsm hnat).mp hMRT
  rw [horth] at hres
  have hproj : G = (centeredNaturalItoRangeProjection hB hsm hnat G :
      (CameronMartin.expectationMap P).ker) :=
    sub_eq_zero.mp (by simpa using hres)
  apply Subtype.ext
  rw [centeredNaturalItoIntegralIsometry_apply,
    naturalItoIntegral_bestNaturalItoIntegrand]
  exact congrArg Subtype.val hproj.symm
end Malliavin
