-- Prove2me | solution 1 for Malliavin.elementaryPredictable_adaptedIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:03:34.119842+00:00
-- url     : https://prove2.me/submissions/69c47517-83f5-4fd2-9af5-bf105b96edcc

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F) :
    (elementaryPredictable (P := P) 𝓕 a b (adaptedIndicator (P := P) 𝓕 a hF) :
        TimeProcessL2 P) =
      indicatorConstLp (μ := nonnegativeLebesgueMeasure.prod P) 2
        (measurableSet_Ioc.prod (𝓕.le a F hF))
        (by
          rw [Measure.prod_prod (μ := nonnegativeLebesgueMeasure) (ν := P)]
          exact ENNReal.mul_ne_top
            (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (measure_ne_top P F))
        (1 : ℝ) := by
  apply Lp.ext
  have hFprod : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (adaptedIndicator (P := P) 𝓕 a hF : W → ℝ) p.2 =
        F.indicator (1 : W → ℝ) p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (adaptedIndicator_coeFn (P := P) 𝓕 a hF)
  filter_upwards [elementaryPredictable_coeFn (P := P) 𝓕 a b
      (adaptedIndicator (P := P) 𝓕 a hF), hFprod,
    indicatorConstLp_coeFn (p := 2)
      (hs := measurableSet_Ioc.prod (𝓕.le a F hF))
      (hμs := by
        rw [Measure.prod_prod (μ := nonnegativeLebesgueMeasure) (ν := P)]
        exact ENNReal.mul_ne_top
          (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (measure_ne_top P F))
      (c := (1 : ℝ))] with p helem hFind hrect
  rw [helem, hrect, hFind]
  by_cases ht : p.1 ∈ Set.Ioc a b <;>
    by_cases hw : p.2 ∈ F <;> simp [ht, hw]
end Malliavin
