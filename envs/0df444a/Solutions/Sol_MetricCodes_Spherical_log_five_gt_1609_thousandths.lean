-- Prove2me | solution 1 for MetricCodes.Spherical.log_five_gt_1609_thousandths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/2f662db6-60a9-4908-b56f-db39432b4c7e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_ratio_lower

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution :
    (1609 : ℝ) / 1000 < Real.log 5 := by
  calc
    (1609 : ℝ) / 1000 <
        MetricCodes.Numerics.logSeriesLower (2 / 3) 14 := by
          norm_num [MetricCodes.Numerics.logSeriesLower,
            Finset.sum_range_succ]
    _ ≤ Real.log (((1 : ℝ) + 2 / 3) / (1 - 2 / 3)) :=
      MetricCodes.Numerics.log_ratio_lower (by norm_num) (by norm_num) 14
    _ = Real.log 5 := by norm_num
end MetricCodes.Spherical
