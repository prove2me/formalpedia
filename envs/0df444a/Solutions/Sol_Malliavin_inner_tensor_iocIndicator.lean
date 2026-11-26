-- Prove2me | solution 1 for Malliavin.inner_tensor_iocIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:26.280154+00:00
-- url     : https://prove2.me/submissions/13e942cb-c016-4392-acfa-5dcb480d22e6

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution (D : TimeProcessL2 P) (c d : ℝ≥0) (g : Lp ℝ 2 P) :
    ⟪D, tensor (iocIndicator c d) g⟫_ℝ =
      ∫ t in Set.Ioc c d, (∫ ω, D (t, ω) * g ω ∂P) ∂nonnegativeLebesgueMeasure := by
  set T : TimeProcessL2 P := tensor (iocIndicator c d) g with hT
  have hint : Integrable (fun p : ℝ≥0 × W ↦ D p * T p) (nonnegativeLebesgueMeasure.prod P) := by
    have := L2.integrable_inner (𝕜 := ℝ) D T
    simpa [RCLike.inner_apply, conj_trivial, mul_comm] using this
  have hTfn : (T : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p ↦ (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 * g p.2 := by
    have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
        (iocIndicator c d : ℝ≥0 → ℝ) p.1 = (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 :=
      Measure.quasiMeasurePreserving_fst.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
          (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top c d) (c := (1 : ℝ)))
    filter_upwards [coeFn_tensor (iocIndicator c d) g, hg] with p hp hg'
    rw [hp, hg']
  have hint' : Integrable (fun p : ℝ≥0 × W ↦
      D p * ((Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 * g p.2))
      (nonnegativeLebesgueMeasure.prod P) :=
    hint.congr (hTfn.mono fun p hp ↦ by dsimp only; rw [hp])
  calc ⟪D, T⟫_ℝ
      = ∫ p, D p * T p ∂(nonnegativeLebesgueMeasure.prod P) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards with p
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    _ = ∫ p : ℝ≥0 × W, D p * ((Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 * g p.2)
          ∂(nonnegativeLebesgueMeasure.prod P) :=
        integral_congr_ae (hTfn.mono fun p hp ↦ by dsimp only; rw [hp])
    _ = ∫ t, ∫ ω, D (t, ω) * ((Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) t * g ω) ∂P
          ∂nonnegativeLebesgueMeasure := integral_prod _ hint'
    _ = ∫ t, (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) t * ∫ ω, D (t, ω) * g ω ∂P
          ∂nonnegativeLebesgueMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        rw [← integral_const_mul]
        congr 1
        funext ω
        ring
    _ = ∫ t, (Set.Ioc c d).indicator (fun t ↦ ∫ ω, D (t, ω) * g ω ∂P) t
          ∂nonnegativeLebesgueMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ Set.Ioc c d <;> simp [ht]
    _ = ∫ t in Set.Ioc c d, (∫ ω, D (t, ω) * g ω ∂P) ∂nonnegativeLebesgueMeasure :=
        integral_indicator measurableSet_Ioc
end Malliavin
