-- Prove2me | solution 1 for Malliavin.inner_elementaryPredictable_adaptedIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:49.664444+00:00
-- url     : https://prove2.me/submissions/20d32499-42cb-4a9b-93e5-7b7e44ee15d4

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
import Theorems.Thm_Malliavin_adaptedIndicator_coeFn
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_elementaryPredictable_coeFn
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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F)
    (g : PredictableProcessL2 𝓕 P) :
    ⟪elementaryPredictable 𝓕 a b (adaptedIndicator (P := P) 𝓕 a hF), g⟫_ℝ =
      ∫ z in Set.Ioc a b ×ˢ F, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P := by
  rw [Submodule.coe_inner, L2.inner_def]
  have hproc := elementaryPredictable_coeFn 𝓕 a b
    (adaptedIndicator (P := P) 𝓕 a hF)
  have hcoef : ∀ᵐ z : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (adaptedIndicator (P := P) 𝓕 a hF : W → ℝ) z.2 =
        F.indicator (fun _ ↦ (1 : ℝ)) z.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (adaptedIndicator_coeFn (P := P) 𝓕 a hF)
  have hae : ∀ᵐ z ∂nonnegativeLebesgueMeasure.prod P,
      (⟪(elementaryPredictable 𝓕 a b
          (adaptedIndicator (P := P) 𝓕 a hF) : ℝ≥0 × W → ℝ) z,
        (g : ℝ≥0 × W → ℝ) z⟫_ℝ : ℝ) =
        (Set.Ioc a b ×ˢ F).indicator (g : ℝ≥0 × W → ℝ) z := by
    filter_upwards [hproc, hcoef] with z hz hZ
    rw [hz, hZ]
    by_cases ht : z.1 ∈ Set.Ioc a b <;>
      by_cases hw : z.2 ∈ F <;> simp [ht, hw]
  rw [integral_congr_ae hae]
  exact integral_indicator (measurableSet_Ioc.prod (𝓕.le a F hF))
end Malliavin
