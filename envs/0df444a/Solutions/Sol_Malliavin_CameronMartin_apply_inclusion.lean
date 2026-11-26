-- Prove2me | solution 1 for Malliavin.CameronMartin.apply_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:45:14.286656+00:00
-- url     : https://prove2.me/submissions/2e1f1b0c-17d5-4c34-bb47-b0a92d50fe6c

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
theorem _root_.solution (L : StrongDual ℝ W) (h : Space μ) :
    L (inclusion μ h) = @inner ℝ _ _ (ofDual μ L) h := by
  rw [inclusion_apply, ← L.integral_comp_comm
    (integrable_smul_centeredId μ (h : Lp ℝ 2 μ)), Submodule.coe_inner,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [centeredDualToLp_ae_eq μ L] with x hx
  simp only [coe_ofDual]
  rw [hx]
  simp only [centeredId, Pi.sub_apply, id_eq, map_smul, map_sub, smul_eq_mul, RCLike.inner_apply, conj_trivial]
end Malliavin.CameronMartin
