-- Prove2me | solution 1 for MetricCodes.Numerics.log_ratio_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/5065a742-495c-4f07-80b2-b90296394543

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) (m : ℕ) :
    Real.log ((1 + x) / (1 - x)) ≤ logSeriesUpper x m := by
  have h := Real.log_div_le_sum_range_add hx hx' m
  unfold logSeriesUpper logSeriesLower
  nlinarith
end MetricCodes.Numerics
