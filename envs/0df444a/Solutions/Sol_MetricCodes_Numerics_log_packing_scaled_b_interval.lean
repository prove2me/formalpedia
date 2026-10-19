-- Prove2me | solution 1 for MetricCodes.Numerics.log_packing_scaled_b_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/63d98ec1-1f37-4e30-ad58-f82639c36325

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
    (245908946257167831 : ℝ) / 10 ^ 18 < Real.log (256 * packingB) ∧
      Real.log (256 * packingB) < (245908946257167832 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (54449830127 : ℝ) / 445074830127) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
