-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularQuadratic_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/ba3c923c-ed55-4579-a5e0-bdbbf6366bdb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution (R : ℝ) :
    Continuous (angularQuadratic R) := by
  unfold angularQuadratic
  fun_prop
end MetricCodes.Spherical.HigherHierarchyChebyshev
