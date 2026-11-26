-- Prove2me | solution 1 for Malliavin.CameronMartin.inclusion_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:22.372957+00:00
-- url     : https://prove2.me/submissions/112f9506-cf8a-4483-a488-07df07c4d5c2

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_CameronMartin
import Theorems.Thm_Malliavin_CameronMartin_denseRange_ofDual
import Theorems.Thm_Malliavin_CameronMartin_apply_inclusion

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
theorem _root_.solution : Function.Injective (inclusion μ) := by
  intro h k hhk
  apply (denseRange_ofDual μ).eq_of_inner_right ℝ
  intro L
  rw [← apply_inclusion μ L h, ← apply_inclusion μ L k, hhk]
end Malliavin.CameronMartin
