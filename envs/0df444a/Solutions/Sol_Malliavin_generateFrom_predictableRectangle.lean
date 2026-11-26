-- Prove2me | solution 1 for Malliavin.generateFrom_predictableRectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:35.591642+00:00
-- url     : https://prove2.me/submissions/66f6d3b6-2d61-44e8-bd89-52de1d8b2eee

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
    MeasurableSpace.generateFrom (predictableRectangle 𝓕) = 𝓕.predictable := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro S (⟨F₀, hF₀, rfl⟩ | ⟨a, b, F, _hab, hF, rfl⟩)
    · exact measurableSet_predictable_singleton_bot_prod hF₀
    · exact measurableSet_predictable_Ioc_prod a b hF
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨A, hA, rfl⟩)
    · intro i A hA
      obtain ⟨seq, _hmono, htends⟩ :=
        Filter.exists_seq_monotone_tendsto_atTop_atTop ℝ≥0
      have hIoi : (Set.Ioi i : Set ℝ≥0) = ⋃ n : ℕ, Set.Ioc i (seq n) := by
        ext s
        simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
        refine ⟨fun his ↦ ?_, fun ⟨_, h, _⟩ ↦ h⟩
        rw [Filter.tendsto_atTop_atTop] at htends
        obtain ⟨n, hn⟩ := htends s
        exact ⟨n, his, hn n le_rfl⟩
      rw [hIoi, Set.iUnion_prod_const]
      refine MeasurableSet.iUnion fun n ↦ ?_
      by_cases hin : i < seq n
      · exact MeasurableSpace.measurableSet_generateFrom
          (Or.inr ⟨i, seq n, A, hin, hA, rfl⟩)
      · have hempty : Set.Ioc i (seq n) ×ˢ A = (∅ : Set (ℝ≥0 × W)) := by
          rw [Set.Ioc_eq_empty_of_le (not_lt.mp hin), Set.empty_prod]
        rw [hempty]
        exact @MeasurableSet.empty _
          (MeasurableSpace.generateFrom (predictableRectangle 𝓕))
end Malliavin
