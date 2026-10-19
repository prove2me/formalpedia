-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_logb_choose_longitudinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/f37092e5-f5eb-4589-a9d5-089b3fce0be6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_log_choose_longitudinal

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (n.choose (longitudinalDegree a n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  have h := (tendsto_log_choose_longitudinal ha ha').div_const (Real.log 2)
  rw [← binaryEntropy_eq_binEntropy_div_log a] at h
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold Real.logb
  ring
end MetricCodes.Hamming
