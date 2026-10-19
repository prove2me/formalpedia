-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_logMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/78e95330-9c85-43c0-8e34-f5ef3313b4aa

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_comparisonDensity_log_intervalIntegral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_integral_eq_intervalIntegral

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
theorem _root_.solution :
    (∫ t, Real.log t ∂comparisonMeasure) = -2 := by
  rw [comparisonMeasure_integral_eq_intervalIntegral]
  exact MetricCodes.Spherical.HigherHierarchy.Arcsine.comparisonDensity_log_intervalIntegral
end MetricCodes.Spherical.HigherHierarchy.Entropy
