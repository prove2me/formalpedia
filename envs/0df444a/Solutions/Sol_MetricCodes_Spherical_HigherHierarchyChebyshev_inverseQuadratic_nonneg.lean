-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.inverseQuadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/509fe037-9aa6-4b39-9fb8-da9fd728c7ce

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ inverseQuadratic x := by
  have hrad : 0 ≤ 1 + 4 * x := by linarith
  have hsqrt := Real.sqrt_nonneg (1 + 4 * x)
  have hsq := Real.sq_sqrt hrad
  unfold inverseQuadratic
  nlinarith
end MetricCodes.Spherical.HigherHierarchyChebyshev
