-- Prove2me | solution 1 for Malliavin.CameronMartin.centeredDualToLp_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:42:50.397701+00:00
-- url     : https://prove2.me/submissions/e504746d-e149-4582-a0b1-aadbd541787c

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_CameronMartin

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
theorem _root_.solution (L : StrongDual ℝ W) :
    ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ) =ᵐ[μ]
      fun x ↦ L x - L (mean μ) := by
  have h_id : MemLp id 2 μ := IsGaussian.memLp_id μ 2 (by norm_num)
  have h_toLp :
      ((StrongDual.toLp μ 2 L : Lp ℝ 2 μ) : W → ℝ) =ᵐ[μ] L := by
    simpa only [StrongDual.toLp_apply h_id, id_eq] using
      MemLp.coeFn_toLp (h_id.continuousLinearMap_comp L)
  have h_const :
      ((Lp.constL 2 μ ℝ (L (mean μ)) : Lp ℝ 2 μ) : W → ℝ) =ᵐ[μ]
        Function.const W (L (mean μ)) := by
    simpa only [Lp.constL_apply] using Lp.coeFn_const 2 μ (L (mean μ))
  unfold centeredDualToLp
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  filter_upwards [Lp.coeFn_sub (StrongDual.toLp μ 2 L)
      (Lp.constL 2 μ ℝ (L (mean μ))), h_toLp, h_const] with x hsub hL hc
  simpa [hL, hc, Function.const_apply] using hsub
end Malliavin.CameronMartin
