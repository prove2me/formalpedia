-- Prove2me | solution 1 for Malliavin.CameronMartin.law_eq_centeredGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:29.538556+00:00
-- url     : https://prove2.me/submissions/22eeefdd-707d-40ed-a9f3-09296447eac0

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply


attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology
noncomputable section
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8
namespace Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
private theorem variance_coe_L2_eq_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp ℝ 2 μ) (hf₀ : ∫ x, f x ∂μ = 0) :
    Var[(f : Ω → ℝ); μ] = ‖f‖ ^ 2 := by
  rw [variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable, hf₀]
  simp only [sub_zero]
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  congr 1
  funext x
  simp only [pow_two, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq,
    abs_mul_abs_self]
end Malliavin.CameronMartin
end
end

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology
noncomputable section
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8
open Malliavin Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin.CameronMartin
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp ℝ 2 μ)
    (hfG : HasGaussianLaw (f : Ω → ℝ) μ) (hf₀ : ∫ x, f x ∂μ = 0) :
    μ.map (f : Ω → ℝ) = gaussianReal 0 (‖f‖₊ ^ 2) := by
  rw [hfG.map_eq_gaussianReal, hf₀, variance_coe_L2_eq_norm_sq μ f hf₀]
  congr 1
  apply NNReal.eq
  simp only [Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_pow, coe_nnnorm]
end Malliavin.CameronMartin
