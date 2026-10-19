-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.quadraticCoordinate_ambient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/7cafa43c-3635-467f-b86d-22857bbcbcc9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_pole_pos
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
    (r : ℕ) (i : Fin (r + 1)) :
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
      (ambient R r i) = pole R (r + 1) i.val := by
  unfold ambient
  exact quadraticCoordinate_inverseQuadratic
    (pole_pos hR (Nat.zero_lt_succ r) i.isLt).le
end MetricCodes.Spherical.HigherHierarchyChebyshev
