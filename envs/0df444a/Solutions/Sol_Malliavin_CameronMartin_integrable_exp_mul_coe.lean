-- Prove2me | solution 1 for Malliavin.CameronMartin.integrable_exp_mul_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:16.290854+00:00
-- url     : https://prove2.me/submissions/e0e17075-5b6e-4217-b375-e391f981b857

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_integrable_exp_coe

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
theorem _root_.solution (h : Space μ) (c : ℝ) :
    Integrable (fun x ↦ Real.exp (c * (h : Lp ℝ 2 μ) x)) μ := by
  refine (integrable_exp_coe μ (c • h)).congr ?_
  filter_upwards [Lp.coeFn_smul c (h : Lp ℝ 2 μ)] with x hx
  rw [Submodule.coe_smul, hx, Pi.smul_apply, smul_eq_mul]
end Malliavin.CameronMartin
