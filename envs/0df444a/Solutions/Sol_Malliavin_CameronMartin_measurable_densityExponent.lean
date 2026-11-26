-- Prove2me | solution 1 for Malliavin.CameronMartin.measurable_densityExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:35.445669+00:00
-- url     : https://prove2.me/submissions/e8c30210-d206-4ef6-9994-ad0129c164ab

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem

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
    Measurable (densityExponent μ h) := by
  exact (Lp.stronglyMeasurable (h : Lp ℝ 2 μ)).measurable.sub_const _
end Malliavin.CameronMartin
