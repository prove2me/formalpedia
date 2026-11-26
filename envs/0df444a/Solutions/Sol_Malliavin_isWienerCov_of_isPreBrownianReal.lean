-- Prove2me | solution 1 for Malliavin.isWienerCov_of_isPreBrownianReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:15.638296+00:00
-- url     : https://prove2.me/submissions/730e904b-69fd-48c6-90c0-3144a5f0033c

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
namespace Malliavin
theorem _root_.solution {W : ℝ≥0 → Ω → ℝ}
    (hW : ProbabilityTheory.IsPreBrownianReal W volume) : IsWienerCov W where
  integrable_W := hW.integrable_eval
  integrable_prod := fun s t =>
    (hW.isGaussianProcess.hasGaussianLaw_eval s).memLp_two.integrable_mul
      (hW.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  mean_zero := hW.integral_eval
  covariance := by
    let _ : IsProbabilityMeasure (volume : Measure Ω) :=
      hW.isGaussianProcess.isProbabilityMeasure
    intro s t
    have hs := (hW.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    have ht := (hW.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
    have hcov := hW.covariance_eval s t
    rw [ProbabilityTheory.covariance_eq_sub hs ht, hW.integral_eval, hW.integral_eval,
      mul_zero, sub_zero] at hcov
    exact hcov
end Malliavin
