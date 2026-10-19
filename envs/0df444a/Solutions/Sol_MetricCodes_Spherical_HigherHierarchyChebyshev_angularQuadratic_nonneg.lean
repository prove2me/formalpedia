-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularQuadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/b0d6cd31-b9f1-4906-8719-bec127f4f47a

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
theorem _root_.solution {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    0 ≤ angularQuadratic R t := by
  unfold angularQuadratic
  exact mul_nonneg (by positivity)
    (by linarith [Real.neg_one_le_cos (Real.pi * t)])
end MetricCodes.Spherical.HigherHierarchyChebyshev
