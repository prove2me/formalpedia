-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_complementShellWeight_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/efa6f0f8-8d29-4dd6-9530-dd43e8e051cb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_complement_longitudinal_ratio

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
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        ((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  simpa [shellWeight] using
    MetricCodes.Hamming.tendsto_complement_longitudinal_ratio ha ha'
end MetricCodes.Johnson.Asymptotics
