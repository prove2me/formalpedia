-- Prove2me | solution 1 for MetricCodes.Numerics.log_interval_of_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/8caec229-b8c3-44ec-b5b9-c00b1c5bfe03

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_ratio_lower
import Theorems.Thm_MetricCodes_Numerics_log_ratio_upper

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution {r x lo hi : ℝ} (m : ℕ)
    (hx : 0 ≤ x) (hx' : x < 1)
    (hr : (1 + x) / (1 - x) = r)
    (hlo : lo < logSeriesLower x m)
    (hhi : logSeriesUpper x m < hi) :
    lo < Real.log r ∧ Real.log r < hi := by
  constructor
  · calc
      lo < logSeriesLower x m := hlo
      _ ≤ Real.log ((1 + x) / (1 - x)) := log_ratio_lower hx hx' m
      _ = Real.log r := by rw [hr]
  · calc
      Real.log r = Real.log ((1 + x) / (1 - x)) := by rw [hr]
      _ ≤ logSeriesUpper x m := log_ratio_upper hx hx' m
      _ < hi := hhi
end MetricCodes.Numerics
