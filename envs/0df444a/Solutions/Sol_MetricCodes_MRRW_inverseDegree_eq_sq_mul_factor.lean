-- Prove2me | solution 1 for MetricCodes.MRRW.inverseDegree_eq_sq_mul_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/cfa46857-742f-4eee-ab92-e7028b5e9252

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {r : ℝ} (hr : r ^ 2 ≤ 1) :
    inverseDegree r = r * (r * inverseVarianceFactor r) := by
  have hradical : 0 ≤ 1 - r ^ 2 := by linarith
  have hsquare := Real.sq_sqrt hradical
  have hroot : 0 ≤ Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_nonneg _
  have hdenominator :
      1 + Real.sqrt (1 - r ^ 2) ≠ 0 := by
    positivity
  unfold inverseDegree inverseVarianceFactor
  field_simp [hdenominator]
  nlinarith
end MetricCodes.MRRW
