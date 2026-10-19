-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.spectralAtom_inverseQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/247ec199-103b-4c4c-81d4-b2228403e9d9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_quadraticCoordinate_inverseQuadratic

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
    MetricCodes.Spherical.HigherHierarchy.spectralAtom
      (inverseQuadratic x) =
      Real.sqrt x / Real.sqrt (1 + 4 * x) := by
  unfold MetricCodes.Spherical.HigherHierarchy.spectralAtom
  rw [quadraticCoordinate_inverseQuadratic hx]
  unfold inverseQuadratic
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev
