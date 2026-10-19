-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.inverseQuadratic_quadraticCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/ab4344e0-0c00-4644-9446-d2c278c5c395

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter
open scoped Topology BigOperators Interval
open MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) :
    inverseQuadratic (a * (1 + a)) = a := by
  unfold inverseQuadratic
  have hsquare : 1 + 4 * (a * (1 + a)) = (1 + 2 * a) ^ 2 := by
    ring
  rw [hsquare, Real.sqrt_sq (by linarith)]
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
