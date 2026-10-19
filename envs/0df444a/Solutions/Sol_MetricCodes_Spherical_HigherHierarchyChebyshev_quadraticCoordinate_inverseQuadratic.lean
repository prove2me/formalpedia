-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.quadraticCoordinate_inverseQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/e1e5c655-a8f1-4761-9597-3b6943bbf1cb

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
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
      (inverseQuadratic x) = x := by
  have hrad : 0 ≤ 1 + 4 * x := by linarith
  have hsq := Real.sq_sqrt hrad
  unfold MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
    inverseQuadratic
  nlinarith
end MetricCodes.Spherical.HigherHierarchyChebyshev
