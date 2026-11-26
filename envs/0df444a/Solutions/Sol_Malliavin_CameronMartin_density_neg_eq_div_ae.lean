-- Prove2me | solution 1 for Malliavin.CameronMartin.density_neg_eq_div_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:37.216248+00:00
-- url     : https://prove2.me/submissions/17874a24-fef7-4bfb-9d62-1f727b13b623

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_density_ne_zero
import Theorems.Thm_Malliavin_CameronMartin_density_ne_top
import Theorems.Thm_Malliavin_CameronMartin_density_mul_neg_ae

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
omit [CompleteSpace W] [SecondCountableTopology W]
namespace Malliavin.CameronMartin
theorem _root_.solution (h : Space μ) :
    density μ (-h) =ᵐ[μ]
      fun x ↦ ENNReal.ofReal (Real.exp (-‖h‖ ^ 2)) / density μ h x := by
  filter_upwards [density_mul_neg_ae μ h] with x hx
  apply (ENNReal.eq_div_iff (density_ne_zero μ h x)
    (density_ne_top μ h x)).2
  exact hx
end Malliavin.CameronMartin
