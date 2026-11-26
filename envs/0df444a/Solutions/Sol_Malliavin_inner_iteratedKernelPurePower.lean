-- Prove2me | solution 1 for Malliavin.inner_iteratedKernelPurePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:45.399681+00:00
-- url     : https://prove2.me/submissions/65bae2d7-15c1-468d-be96-3be1960d1f39

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
import Theorems.Thm_Malliavin_coeFn_iteratedKernelPurePower
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
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
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
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
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
namespace Malliavin
theorem _root_.solution (n : ℕ)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (iteratedKernelPurePower n f) (iteratedKernelPurePower n g) =
      inner ℝ f g ^ n := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    (∫ t, inner ℝ (iteratedKernelPurePower n f t)
        (iteratedKernelPurePower n g t) ∂iteratedKernelMeasure n) =
        ∫ t, ∏ i, inner ℝ (f (t i)) (g (t i)) ∂iteratedKernelMeasure n := by
      apply integral_congr_ae
      filter_upwards [coeFn_iteratedKernelPurePower n f,
        coeFn_iteratedKernelPurePower n g] with t hf hg
      rw [hf, hg]
      simp only [iteratedKernelPurePowerFun, RCLike.inner_apply, conj_trivial,
        Finset.prod_mul_distrib]
    _ = (∫ t, inner ℝ (f t) (g t) ∂nonnegativeLebesgueMeasure) ^ n := by
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin n)
          (μ := nonnegativeLebesgueMeasure) (fun t ↦ inner ℝ (f t) (g t)))
end Malliavin
