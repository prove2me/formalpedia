-- Prove2me | solution 1 for Malliavin.isPiSystem_predictableRectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:32.620531+00:00
-- url     : https://prove2.me/submissions/e537073f-699c-4e68-a1af-e83a9e61ed39

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    IsPiSystem (predictableRectangle 𝓕) := by
  rintro S₁ hS₁ S₂ hS₂ hne
  rcases hS₁ with ⟨F₀₁, hF₀₁, rfl⟩ | ⟨a₁, b₁, F₁, hab₁, hF₁, rfl⟩
  all_goals
    rcases hS₂ with ⟨F₀₂, hF₀₂, rfl⟩ | ⟨a₂, b₂, F₂, hab₂, hF₂, rfl⟩
  · left
    refine ⟨F₀₁ ∩ F₀₂, hF₀₁.inter hF₀₂, ?_⟩
    rw [Set.prod_inter_prod, Set.inter_self]
  · exfalso
    obtain ⟨⟨t, w⟩, ht⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_Ioc] at ht
    obtain ⟨⟨rfl, _⟩, ⟨ha₂, _⟩, _⟩ := ht
    exact not_lt_bot ha₂
  · exfalso
    obtain ⟨⟨t, w⟩, ht⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc,
      Set.mem_singleton_iff] at ht
    obtain ⟨⟨⟨ha₁, _⟩, _⟩, rfl, _⟩ := ht
    exact not_lt_bot ha₁
  · right
    obtain ⟨⟨t, w⟩, ht⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc] at ht
    obtain ⟨⟨⟨ha₁, hb₁⟩, _⟩, ⟨ha₂, hb₂⟩, _⟩ := ht
    have hlt : a₁ ⊔ a₂ < b₁ ⊓ b₂ :=
      lt_of_lt_of_le (max_lt ha₁ ha₂) (le_min hb₁ hb₂)
    refine ⟨a₁ ⊔ a₂, b₁ ⊓ b₂, F₁ ∩ F₂, hlt, ?_, ?_⟩
    · exact (𝓕.mono (le_max_left a₁ a₂) _ hF₁).inter
        (𝓕.mono (le_max_right a₁ a₂) _ hF₂)
    · rw [Set.prod_inter_prod, Set.Ioc_inter_Ioc]
end Malliavin
