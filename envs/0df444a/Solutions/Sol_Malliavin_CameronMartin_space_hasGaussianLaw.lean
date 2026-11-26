-- Prove2me | solution 1 for Malliavin.CameronMartin.space_hasGaussianLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:06.5014+00:00
-- url     : https://prove2.me/submissions/e54b7be2-7ca6-4caf-b098-ff4492ff502d

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
import Theorems.Thm_Malliavin_CameronMartin_hasGaussianLaw_L2_limit_of_centered
import Theorems.Thm_Malliavin_CameronMartin_centeredDualToLp_ae_eq
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
private theorem hasGaussianLaw_centeredDualToLp (L : StrongDual ℝ W) :
    HasGaussianLaw ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ) μ := by
  apply HasGaussianLaw.congr (Y :=
    ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ)) ?_
    (centeredDualToLp_ae_eq μ L).symm
  refine ⟨?_⟩
  have h_eq :
      μ.map (fun x ↦ L x - L (mean μ)) =
        (μ.map L).map (fun y ↦ y - L (mean μ)) := by
    calc
      μ.map (fun x ↦ L x - L (mean μ)) =
          μ.map ((fun y ↦ y - L (mean μ)) ∘ L) := rfl
      _ = (μ.map L).map (fun y ↦ y - L (mean μ)) :=
        (Measure.map_map (measurable_id.sub_const _) L.measurable).symm
  rw [h_eq]
  infer_instance
private theorem integral_centeredDualToLp_eq_zero (L : StrongDual ℝ W) :
    ∫ x, (centeredDualToLp μ L : Lp ℝ 2 μ) x ∂μ = 0 := by
  rw [integral_congr_ae (centeredDualToLp_ae_eq μ L)]
  have hL : Integrable L μ :=
    memLp_one_iff_integrable.mp (IsGaussian.memLp_dual μ L 1 (by norm_num))
  rw [integral_sub hL (integrable_const (L (mean μ)))]
  rw [IsGaussian.integral_dual L]
  simp only [mean, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]
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
theorem _root_.solution (h : Space μ) :
    HasGaussianLaw ((h : Lp ℝ 2 μ) : W → ℝ) μ := by
  rcases mem_closure_iff_seq_limit.mp h.property with ⟨f, hf_range, hf_tendsto⟩
  choose L hL using hf_range
  apply hasGaussianLaw_L2_limit_of_centered μ hf_tendsto
  · intro n
    rw [← hL n]
    exact hasGaussianLaw_centeredDualToLp μ (L n)
  · intro n
    rw [← hL n]
    exact integral_centeredDualToLp_eq_zero μ (L n)
end Malliavin.CameronMartin
