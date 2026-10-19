-- Prove2me | solution 1 for MetricCodes.Numerics.log_kissing_one_add_b_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/062a9222-a933-42e1-a8fe-30c3d0c9ba70

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
    (3695990739373266 : ℝ) / 10 ^ 18 < Real.log (1 + kissingB) ∧
      Real.log (1 + kissingB) < (3695990739373267 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (5785670837 : ℝ) / 3130785670837) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
