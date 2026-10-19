-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.inverseQuadratic_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/60e79e3d-221a-4fe7-a551-d249ef620a76

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_inverseQuadratic_nonneg
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
theorem _root_.solution :
    StrictMonoOn inverseQuadratic (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  by_contra hnot
  have hle : inverseQuadratic y ≤ inverseQuadratic x := le_of_not_gt hnot
  have hquad :=
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate_strictMonoOn.monotoneOn
      (inverseQuadratic_nonneg hy) (inverseQuadratic_nonneg hx) hle
  rw [quadraticCoordinate_inverseQuadratic hy,
    quadraticCoordinate_inverseQuadratic hx] at hquad
  linarith
end MetricCodes.Spherical.HigherHierarchyChebyshev
