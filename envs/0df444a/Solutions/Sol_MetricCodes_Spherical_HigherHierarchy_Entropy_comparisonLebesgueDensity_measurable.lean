-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparisonLebesgueDensity_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/f837b1fb-7918-4fee-a203-5d7502613334

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
theorem _root_.solution :
    Measurable comparisonLebesgueDensity := by
  unfold comparisonLebesgueDensity
  apply Measurable.ite
    ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const))
  · fun_prop
  · fun_prop
end MetricCodes.Spherical.HigherHierarchy.Entropy
