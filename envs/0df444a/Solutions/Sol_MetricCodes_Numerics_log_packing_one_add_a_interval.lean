-- Prove2me | solution 1 for MetricCodes.Numerics.log_packing_one_add_a_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/4cdbdaab-f2c8-4c4d-ae91-a003b7b70ca4

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
    (100432859923757990 : ℝ) / 10 ^ 18 < Real.log (1 + packingA) ∧
      Real.log (1 + packingA) < (100432859923757991 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (528247029133 : ℝ) / 10528247029133) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
