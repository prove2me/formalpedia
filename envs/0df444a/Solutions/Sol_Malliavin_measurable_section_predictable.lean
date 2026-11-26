-- Prove2me | solution 1 for Malliavin.measurable_section_predictable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:04.088656+00:00
-- url     : https://prove2.me/submissions/6139bee2-805c-450f-8a60-c9969c0c8e4b

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
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
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution (t : ℝ≥0) :
    @Measurable W (ℝ≥0 × W) (𝓕 t) 𝓕.predictable (fun ω ↦ (t, ω)) := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_le_iff_le_map]
  refine measurableSpace_le_predictable_of_measurableSet ?_ ?_
  · intro A hA
    rw [MeasurableSpace.map_def]
    rcases eq_or_ne t 0 with ht | ht
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' ({⊥} ×ˢ A) = A := by
        ext ω
        simp only [ht, bot_eq_zero', Set.mem_singleton_iff, Set.mk_preimage_prod_right]
      rw [this]
      exact 𝓕.mono (by simp [ht]) A hA
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' ({⊥} ×ˢ A) = ∅ := by
        ext ω
        simp only [bot_eq_zero', Set.mem_singleton_iff, ht, not_false_eq_true, Set.mk_preimage_prod_right_eq_empty,
    Set.mem_empty_iff_false]
      rw [this]
      exact @MeasurableSet.empty _ (𝓕 t)
  · intro i A hA
    rw [MeasurableSpace.map_def]
    rcases lt_or_ge i t with hit | hit
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' (Set.Ioi i ×ˢ A) = A := by
        ext ω
        simp only [Set.mem_Ioi, hit, Set.mk_preimage_prod_right]
      rw [this]
      exact 𝓕.mono hit.le A hA
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' (Set.Ioi i ×ˢ A) = ∅ := by
        ext ω
        simp only [Set.mem_Ioi, not_lt.mpr hit, not_false_eq_true, Set.mk_preimage_prod_right_eq_empty,
    Set.mem_empty_iff_false]
      rw [this]
      exact @MeasurableSet.empty _ (𝓕 t)
end Malliavin
