-- Prove2me | solution 1 for MetricCodes.Numerics.log_ratio_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/851a0d1e-964f-4dfb-ae9f-785e977f1264

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
    logSeriesLower x m ≤ Real.log ((1 + x) / (1 - x)) := by
  have h := Real.sum_range_le_log_div hx hx' m
  unfold logSeriesLower
  nlinarith
end MetricCodes.Numerics
