-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.quadraticCoordinate_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/124d8179-4cd9-4c54-b216-9647560bf63e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zero_nonneg
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
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    (r : ℕ) (i : Fin r) :
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
      (stabilizer R r i) = zero R (r + 1) (i.val + 1) := by
  unfold stabilizer
  exact quadraticCoordinate_inverseQuadratic
    (zero_nonneg hR.le (r + 1) (i.val + 1))
end MetricCodes.Spherical.HigherHierarchyChebyshev
