-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Numerics.rational_log_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/cac6672d-32ae-4d85-8aa7-607ddc4b0c97

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_ratio_upper

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
theorem _root_.solution {r hi : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hhi : MetricCodes.Numerics.logSeriesUpper
      ((r - 1) / (r + 1)) m < hi) : Real.log r < hi := by
  have hden : 0 < r + 1 := by linarith
  have hx : 0 ≤ (r - 1) / (r + 1) :=
    div_nonneg (sub_nonneg.mpr hr) hden.le
  have hx' : (r - 1) / (r + 1) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  calc
    Real.log r = Real.log
      ((1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1))) := by
        congr 1
        field_simp; ring
    _ ≤ MetricCodes.Numerics.logSeriesUpper
      ((r - 1) / (r + 1)) m :=
        MetricCodes.Numerics.log_ratio_upper hx hx' m
    _ < hi := hhi
end MetricCodes.Spherical.HigherHierarchy.Numerics
