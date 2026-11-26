-- Prove2me | solution 1 for Malliavin.CameronMartin.hasGaussianLaw_L2_limit_of_centered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:16.800071+00:00
-- url     : https://prove2.me/submissions/ea452c30-9509-4e86-a30e-98f1789bcb69

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
import Theorems.Thm_Malliavin_CameronMartin_law_eq_centeredGaussian
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
private lemma tendsto_centeredGaussianPM {v : ℕ → ℝ≥0} {v₀ : ℝ≥0}
    (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n ↦ centeredGaussianPM (v n)) atTop (𝓝 (centeredGaussianPM v₀)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simp only [centeredGaussianPM, ProbabilityMeasure.coe_mk,
    charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  have hvR : Tendsto (fun n ↦ (v n : ℝ)) atTop (𝓝 (v₀ : ℝ)) :=
    NNReal.tendsto_coe.mpr hv
  exact (((hvR.ofReal.mul_const ((t : ℂ) ^ 2)).div_const 2).neg).cexp
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
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (hfg : Tendsto f atTop (𝓝 g))
    (hfG : ∀ n, HasGaussianLaw (f n : Ω → ℝ) μ)
    (hf₀ : ∀ n, ∫ x, f n x ∂μ = 0) : HasGaussianLaw (g : Ω → ℝ) μ := by
  have hdist := (tendstoInMeasure_of_tendsto_Lp hfg).tendstoInDistribution
    (fun n ↦ (Lp.aestronglyMeasurable (f n)).aemeasurable)
  have hlaw : Tendsto
      (fun n ↦ lawPM μ (f n : Ω → ℝ)
        (Lp.aestronglyMeasurable (f n)).aemeasurable) atTop
      (𝓝 (lawPM μ (g : Ω → ℝ) (Lp.aestronglyMeasurable g).aemeasurable)) :=
    hdist.tendsto
  have hv : Tendsto (fun n ↦ ‖f n‖₊ ^ 2) atTop (𝓝 (‖g‖₊ ^ 2)) :=
    hfg.nnnorm.pow 2
  have hgauss := tendsto_centeredGaussianPM hv
  have heq : (fun n ↦ lawPM μ (f n : Ω → ℝ)
      (Lp.aestronglyMeasurable (f n)).aemeasurable) =
      fun n ↦ centeredGaussianPM (‖f n‖₊ ^ 2) := by
    funext n
    apply Subtype.ext
    exact law_eq_centeredGaussian μ (f n) (hfG n) (hf₀ n)
  rw [heq] at hlaw
  have hprobEq := tendsto_nhds_unique hlaw hgauss
  have hmeasureEq : μ.map (g : Ω → ℝ) = gaussianReal 0 (‖g‖₊ ^ 2) :=
    congrArg Subtype.val hprobEq
  refine ⟨?_⟩
  rw [hmeasureEq]
  infer_instance
end Malliavin.CameronMartin
