-- Prove2me | solution 1 for MetricCodes.Numerics.log_two_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/2da71820-813b-4110-b216-32d9548e0d36

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_interval_of_series

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution :
    (693147180559945309 : ℝ) / 10 ^ 18 < Real.log 2 ∧
      Real.log 2 < (693147180559945310 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series (x := (1 : ℝ) / 3) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
