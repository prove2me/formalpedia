-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_iteratedKernelPurePower_boxKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:27.926669+00:00
-- url     : https://prove2.me/submissions/61d82369-a35d-4880-a4c9-e145e9989dae

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_coeFn_iteratedKernelPurePower
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
attribute [local simp] Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (u v : Fin n → ℝ≥0) :
    inner ℝ (iteratedKernelPurePower n f) (boxKernel u v) =
      ∏ i, inner ℝ f (iocIndicator (u i) (v i)) := by
  rw [MeasureTheory.L2.inner_def]
  have hpure := coeFn_iteratedKernelPurePower n f
  have hbox : (boxKernel u v : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
      (orderedBox u v).indicator fun _ ↦ (1 : ℝ) :=
    indicatorConstLp_coeFn
  calc
    (∫ t, inner ℝ (iteratedKernelPurePower n f t) (boxKernel u v t)
        ∂iteratedKernelMeasure n) =
        ∫ t, ∏ i, f (t i) *
          (Set.Ioc (u i) (v i)).indicator (fun _ ↦ (1 : ℝ)) (t i)
          ∂iteratedKernelMeasure n := by
      apply integral_congr_ae
      filter_upwards [hpure, hbox] with t hpure_t hbox_t
      rw [hpure_t, hbox_t]
      simp only [RCLike.inner_apply, conj_trivial, iteratedKernelPurePowerFun]
      by_cases ht : t ∈ orderedBox u v
      · rw [Set.indicator_of_mem ht]
        have hti : ∀ i, t i ∈ Set.Ioc (u i) (v i) := by
          intro i
          exact ht i (Set.mem_univ i)
        simp only [hti, Set.indicator_of_mem, mul_one, one_mul]
      · rw [Set.indicator_of_notMem ht, zero_mul]
        have hnot : ¬ ∀ i, t i ∈ Set.Ioc (u i) (v i) := by
          intro hall
          exact ht fun i _ ↦ hall i
        push Not at hnot
        obtain ⟨i, hi⟩ := hnot
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [Set.indicator_of_notMem hi, mul_zero]
    _ = ∏ i, ∫ x, f x *
          (Set.Ioc (u i) (v i)).indicator (fun _ ↦ (1 : ℝ)) x
          ∂nonnegativeLebesgueMeasure := by
      change (∫ t, ∏ i, f (t i) *
          (Set.Ioc (u i) (v i)).indicator (fun _ ↦ (1 : ℝ)) (t i)
          ∂(Measure.pi fun _ : Fin n ↦ nonnegativeLebesgueMeasure)) = _
      exact integral_fintype_prod_eq_prod
        (E := fun _ : Fin n ↦ ℝ≥0)
        (f := fun i x ↦ f x *
          (Set.Ioc (u i) (v i)).indicator (fun _ ↦ (1 : ℝ)) x)
        (μ := fun _ : Fin n ↦ nonnegativeLebesgueMeasure)
    _ = ∏ i, inner ℝ f (iocIndicator (u i) (v i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top (u i) (v i))
        (c := (1 : ℝ))] with x hx
      unfold iocIndicator
      rw [hx]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
end Malliavin.BrownianIteratedConstruction
