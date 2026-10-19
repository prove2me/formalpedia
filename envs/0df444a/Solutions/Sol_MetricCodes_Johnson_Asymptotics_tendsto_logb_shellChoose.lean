-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_shellChoose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/8c908bf5-ce33-438b-a315-c4b2337d9982

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_choose_longitudinal

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (n.choose (shellWeight a n) : ℝ) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  simpa [shellWeight] using
    MetricCodes.Hamming.tendsto_logb_choose_longitudinal
      h.weight_pos (by linarith [h.weight_lt_half])
end MetricCodes.Johnson.Asymptotics
