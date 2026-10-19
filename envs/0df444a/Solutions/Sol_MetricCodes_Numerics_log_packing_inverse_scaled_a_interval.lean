-- Prove2me | solution 1 for MetricCodes.Numerics.log_packing_inverse_scaled_a_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/2e6dcee7-3cbb-41b2-9cef-673a11be5789

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
    (168187617235226574 : ℝ) / 10 ^ 18 <
        Real.log (1 / (8 * packingA)) ∧
      Real.log (1 / (8 * packingA)) <
        (168187617235226575 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (96752970867 : ℝ) / 1153247029133) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
