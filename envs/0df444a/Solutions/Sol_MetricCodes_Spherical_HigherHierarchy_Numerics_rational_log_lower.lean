-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Numerics.rational_log_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/2cf050fe-cb00-497f-8c4f-8f572da686e0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_ratio_lower

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy.Numerics
namespace MetricCodes.Spherical.HigherHierarchy.Numerics
theorem _root_.solution {r lo : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hlo : lo < MetricCodes.Numerics.logSeriesLower
      ((r - 1) / (r + 1)) m) : lo < Real.log r := by
  have hden : 0 < r + 1 := by linarith
  have hx : 0 ≤ (r - 1) / (r + 1) :=
    div_nonneg (sub_nonneg.mpr hr) hden.le
  have hx' : (r - 1) / (r + 1) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  calc
    lo < MetricCodes.Numerics.logSeriesLower
      ((r - 1) / (r + 1)) m := hlo
    _ ≤ Real.log
      ((1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1))) :=
        MetricCodes.Numerics.log_ratio_lower hx hx' m
    _ = Real.log r := by
      congr 1
      field_simp; ring
end MetricCodes.Spherical.HigherHierarchy.Numerics
