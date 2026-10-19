-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.stabilizer_quadratic_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/3fea3d9b-df58-4953-96c8-ccd905e34b97

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
    (h : Interlacing a b) (i : Fin r) :
    0 < quadraticCoordinate (b i) := by
  unfold quadraticCoordinate
  exact mul_pos (h.stabilizer_pos i) (by linarith [h.stabilizer_pos i])
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
