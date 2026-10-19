-- Prove2me | solution 1 for MetricCodes.Spherical.log_three_lt_1099_thousandths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/29e657e1-79da-4e61-92d3-5e5484becbe4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_ratio_upper

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution :
    Real.log 3 < (1099 : ℝ) / 1000 := by
  calc
    Real.log 3 = Real.log
        (((1 : ℝ) + 1 / 2) / (1 - 1 / 2)) := by norm_num
    _ ≤ MetricCodes.Numerics.logSeriesUpper (1 / 2) 10 :=
      MetricCodes.Numerics.log_ratio_upper (by norm_num) (by norm_num) 10
    _ < (1099 : ℝ) / 1000 := by
      norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Spherical
