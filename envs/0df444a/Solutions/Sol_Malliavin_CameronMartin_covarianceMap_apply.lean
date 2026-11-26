-- Prove2me | solution 1 for Malliavin.CameronMartin.covarianceMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:42:27.12317+00:00
-- url     : https://prove2.me/submissions/0ec425e2-4560-412f-ab8f-ff67c8118609

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
theorem _root_.solution (f : Lp ℝ 2 μ) :
    covarianceMap μ f = ∫ x, f x • centeredId μ x ∂μ := by
  rw [covarianceMap, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_centeredId μ)] with x hx
  simp only [ContinuousLinearMap.lsmul_apply]
  change f x • ((memLp_centeredId μ).toLp (centeredId μ)) x = _
  rw [hx]
end Malliavin.CameronMartin
