-- Prove2me | solution 1 for Malliavin.CameronMartin.inner_ofDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:10:09.618244+00:00
-- url     : https://prove2.me/submissions/d9e84ef0-33b8-492d-90ee-e679d60a87a4

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_CameronMartin
import Theorems.Thm_Malliavin_CameronMartin_centeredDualToLp_ae_eq
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real Topology
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_7
open Malliavin
open Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin.CameronMartin
theorem _root_.solution (L K : StrongDual ℝ W) :
    @inner ℝ _ _ (ofDual μ L) (ofDual μ K) = covarianceBilinDual μ L K := by
  rw [Submodule.coe_inner, L2.inner_def]
  rw [covarianceBilinDual_apply IsGaussian.memLp_two_id]
  apply integral_congr_ae
  filter_upwards [centeredDualToLp_ae_eq μ L,
    centeredDualToLp_ae_eq μ K] with x hL hK
  simp only [coe_ofDual]
  rw [hL, hK]
  rw [IsGaussian.integral_dual L, IsGaussian.integral_dual K]
  simp only [mean, RCLike.inner_apply, conj_trivial]
  ring
end Malliavin.CameronMartin
