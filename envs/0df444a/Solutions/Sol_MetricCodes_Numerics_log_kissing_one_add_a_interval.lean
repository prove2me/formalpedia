-- Prove2me | solution 1 for MetricCodes.Numerics.log_kissing_one_add_a_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/11b09c85-8b1a-43d1-84b8-4c16bc3c3d60

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
    (82226264808038924 : ℝ) / 10 ^ 18 < Real.log (1 + kissingA) ∧
      Real.log (1 + kissingA) < (82226264808038925 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (4285071903373 : ℝ) / 104285071903373) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
