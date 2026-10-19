-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusNormalizer_quadraticCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/23b7c7ff-6d0d-4e42-8bee-678e8769ef9a

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
    radiusNormalizer (a * (1 + a)) =
      (2 / Real.pi) * Real.arcsin (1 / (1 + 2 * a)) := by
  unfold radiusNormalizer
  have hsquare : 4 * (a * (1 + a)) + 1 = (1 + 2 * a) ^ 2 := by
    ring
  rw [hsquare, Real.sqrt_sq (by linarith)]
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
