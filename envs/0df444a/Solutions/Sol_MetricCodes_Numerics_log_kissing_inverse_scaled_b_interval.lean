-- Prove2me | solution 1 for MetricCodes.Numerics.log_kissing_inverse_scaled_b_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/fa279481-ac68-41ba-a844-d149c4618647

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
    (53480621756332520 : ℝ) / 10 ^ 18 <
        Real.log (1 / (256 * kissingB)) ∧
      Real.log (1 / (256 * kissingB)) <
        (53480621756332521 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (158922394 : ℝ) / 5944593231) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
