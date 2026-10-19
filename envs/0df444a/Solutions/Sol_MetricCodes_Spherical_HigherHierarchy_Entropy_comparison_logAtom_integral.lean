-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_logAtom_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/37d6971e-6d63-4ef0-b6ff-461233d55b21

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_comparisonDensity_logAtom_intervalIntegral
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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) :
    (∫ t, Real.log ((t + a * (1 + a)) / t) ∂comparisonMeasure) =
      2 * ((1 + a) * Real.log (1 + a) - a * Real.log a) := by
  rw [comparisonMeasure_integral_eq_intervalIntegral]
  exact
    MetricCodes.Spherical.HigherHierarchy.Arcsine.comparisonDensity_logAtom_intervalIntegral ha
end MetricCodes.Spherical.HigherHierarchy.Entropy
