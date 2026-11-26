-- Prove2me | solution 1 for Malliavin.CameronMartin.exists_integrable_exp_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:00.071801+00:00
-- url     : https://prove2.me/submissions/c5e10c1d-702c-438a-af82-3b634370f4c7

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
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun x ↦ Real.exp (C * ‖x‖ ^ 2)) μ := by
  have h_fernique :
      ∃ C : ℝ, 0 < C ∧ Integrable (fun x ↦ Real.exp (C * ‖x‖ ^ 2)) μ :=
    IsGaussian.exists_integrable_exp_sq μ
  exact h_fernique
end Malliavin.CameronMartin
