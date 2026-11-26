-- Prove2me | solution 1 for Malliavin.CameronMartin.inclusion_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:43:18.895235+00:00
-- url     : https://prove2.me/submissions/a67e79ea-2bde-47e8-a289-9fe71f5d5b6b

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_CameronMartin
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply

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
theorem _root_.solution (h : Space μ) :
    inclusion μ h = ∫ x, (h : Lp ℝ 2 μ) x • centeredId μ x ∂μ :=
  covarianceMap_apply μ (h : Lp ℝ 2 μ)
end Malliavin.CameronMartin
