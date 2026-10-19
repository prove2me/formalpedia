-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparisonMeasure_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/8b0cf6c5-e8b0-42d0-b0fb-4b768a1a2816

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_betaMap_one_half_eq_withDensity

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
    comparisonMeasure = arcsineMeasure.withDensity
      (fun t => ENNReal.ofReal (Real.pi * Real.sqrt t)) := by
  simpa [comparisonMeasure, arcsineMeasure] using
    MetricCodes.Spherical.HigherHierarchy.Arcsine.betaMap_one_half_eq_withDensity
end MetricCodes.Spherical.HigherHierarchy.Entropy
