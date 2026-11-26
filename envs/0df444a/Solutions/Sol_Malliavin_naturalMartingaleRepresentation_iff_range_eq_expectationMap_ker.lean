-- Prove2me | solution 1 for Malliavin.naturalMartingaleRepresentation_iff_range_eq_expectationMap_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:37.437847+00:00
-- url     : https://prove2.me/submissions/c3b4d4c4-b390-415d-acdb-3b7cc121b111

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_range_naturalItoIntegral_le_expectationMap_ker
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
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
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.mem_symmetricSubmodule


attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply

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
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap =
        (CameronMartin.expectationMap P).ker := by
  rw [naturalMartingaleRepresentation_iff_surjective]
  constructor
  · intro hsurj
    apply le_antisymm (range_naturalItoIntegral_le_expectationMap_ker hB hsm hnat)
    intro G hG
    obtain ⟨U, hU⟩ := hsurj ⟨G, hG⟩
    refine ⟨U, ?_⟩
    exact congrArg Subtype.val hU
  · intro hrange G
    have hG : (G : RandomL2 P) ∈
        LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap := by
      rw [hrange]
      exact G.property
    obtain ⟨U, hU⟩ := hG
    refine ⟨U, Subtype.ext ?_⟩
    exact hU
end Malliavin
