-- Prove2me | solution 1 for MetricCodes.Numerics.log_packing_geometric_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/83399f56-fe51-4af5-aaef-f777d268f5ac

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
    (83515566770761640 : ℝ) / 10 ^ 18 <
        Real.log (1 / (2 * (1 - packingS))) ∧
      Real.log (1 / (2 * (1 - packingS))) <
        (83515566770761641 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (4006161647549 : ℝ) / 95993838352451) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingS]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]
end MetricCodes.Numerics
