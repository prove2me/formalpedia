-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_logLikelihood_integrable_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/b87acff0-07a9-4cb5-ae43-416923edfb24

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_logLikelihood_of_density

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Entropy
namespace MetricCodes.Spherical.HigherHierarchy.Entropy
theorem _root_.solution
    (hdensity : comparisonMeasure.rnDeriv arcsineMeasure =ᵐ[arcsineMeasure]
      fun t => ENNReal.ofReal (Real.pi * Real.sqrt t))
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure) :
    Integrable (llr comparisonMeasure arcsineMeasure) comparisonMeasure := by
  rw [integrable_congr (comparison_logLikelihood_of_density hdensity)]
  exact (integrable_const _).add (hlog.div_const 2)
end MetricCodes.Spherical.HigherHierarchy.Entropy
