-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_log_integrable_of_logMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/7b576952-84f6-47e6-b79d-f5f314301b39

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (hmoment : (∫ t, Real.log t ∂comparisonMeasure) = -2) :
    Integrable (fun t : ℝ => Real.log t) comparisonMeasure := by
  by_contra h
  have hzero := integral_undef h
  rw [hmoment] at hzero
  norm_num at hzero
end MetricCodes.Spherical.HigherHierarchy.Entropy
