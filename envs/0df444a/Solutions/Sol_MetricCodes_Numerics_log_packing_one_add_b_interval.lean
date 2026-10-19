-- Prove2me | solution 1 for MetricCodes.Numerics.log_packing_one_add_b_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/b60cb1ad-54b6-4119-924a-1cd543140807

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
    (4982811751137358 : ℝ) / 10 ^ 18 < Real.log (1 + packingB) ∧
      Real.log (1 + packingB) < (4982811751137359 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (249762330127 : ℝ) / 100249762330127) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
