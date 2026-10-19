-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.ambient_quadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/fd3e2e30-7b3b-4bb9-9091-f1dcd69ce1c7

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
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin (r + 1)) :
    0 ≤ quadraticCoordinate (a i) := by
  unfold quadraticCoordinate
  exact mul_nonneg (h.ambient_nonneg i) (by linarith [h.ambient_nonneg i])
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
