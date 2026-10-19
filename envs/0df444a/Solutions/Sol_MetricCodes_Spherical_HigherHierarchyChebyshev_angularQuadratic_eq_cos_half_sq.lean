-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularQuadratic_eq_cos_half_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/9e8c69c1-2755-4010-88e4-c5d5c6d572b6

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
theorem _root_.solution (R t : ℝ) :
    angularQuadratic R t =
      R * Real.cos (Real.pi * t / 2) ^ 2 := by
  have hcos := Real.cos_two_mul (Real.pi * t / 2)
  have harg : 2 * (Real.pi * t / 2) = Real.pi * t := by ring
  rw [harg] at hcos
  unfold angularQuadratic
  rw [hcos]
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev
