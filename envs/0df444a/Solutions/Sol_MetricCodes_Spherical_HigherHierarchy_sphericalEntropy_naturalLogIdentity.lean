-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sphericalEntropy_naturalLogIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/97b868ae-731c-4c3e-9b8b-77bf29491ef0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution (u : ℝ) :
    2 * ((1 + u) * Real.log (1 + u) - u * Real.log u) =
      2 * Real.log 2 * MetricCodes.sphericalEntropy u := by
  have htwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  unfold MetricCodes.sphericalEntropy Real.logb
  field_simp
end MetricCodes.Spherical.HigherHierarchy
