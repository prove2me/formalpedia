-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.quadratic_spectralAtom_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/92ecd489-375e-4147-bd54-1a4b2107ef8a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt
      (quadraticCoordinate u / (quadraticCoordinate u + 1 / 4)) =
        2 * spectralAtom u := by
  have hA : 0 ≤ quadraticCoordinate u := by
    unfold quadraticCoordinate
    positivity
  have hlinear : 0 < 1 + 2 * u := by linarith
  have hden : 0 < quadraticCoordinate u + 1 / 4 := by linarith
  have hroot :
      Real.sqrt (quadraticCoordinate u + 1 / 4) =
        (1 + 2 * u) / 2 := by
    have hsquare := Real.sq_sqrt hden.le
    have hnonneg := Real.sqrt_nonneg
      (quadraticCoordinate u + 1 / 4)
    have htarget :
        ((1 + 2 * u) / 2) ^ 2 = quadraticCoordinate u + 1 / 4 := by
      unfold quadraticCoordinate
      ring
    nlinarith
  rw [Real.sqrt_div hA, hroot]
  unfold spectralAtom
  field_simp
end MetricCodes.Spherical.HigherHierarchy
