-- Prove2me | solution 1 for MetricCodes.Numerics.log_kissing_scaled_a_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/51d9c985-0f68-42a8-8bb2-6ccf3f196a14

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
    (315703048970999865 : ℝ) / 10 ^ 18 < Real.log (16 * kissingA) ∧
      Real.log (16 * kissingA) < (315703048970999866 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (1160071903373 : ℝ) / 7410071903373) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
