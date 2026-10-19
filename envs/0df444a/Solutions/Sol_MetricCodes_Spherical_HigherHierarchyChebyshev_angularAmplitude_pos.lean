-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularAmplitude_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/3a5818ac-353f-48dd-88d4-6f8ee9827dd5

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
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    0 < angularAmplitude R := by
  unfold angularAmplitude
  positivity
end MetricCodes.Spherical.HigherHierarchyChebyshev
