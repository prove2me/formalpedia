-- Prove2me | solution 1 for MetricCodes.Boolean.hammingSqrtDivProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/61eb17c0-b9b1-42c0-803d-fc3b2d2c7975

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (r / (a * b)) =
      (Real.sqrt a)⁻¹ * (Real.sqrt b)⁻¹ * Real.sqrt r := by
  rw [Real.sqrt_div hr, Real.sqrt_mul ha.le]
  field_simp [(Real.sqrt_pos.mpr ha).ne',
    (Real.sqrt_pos.mpr hb).ne']
end MetricCodes.Boolean
