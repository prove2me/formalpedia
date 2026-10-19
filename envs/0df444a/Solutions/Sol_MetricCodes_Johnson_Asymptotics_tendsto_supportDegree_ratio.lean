-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_supportDegree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/10293dcf-5263-4dd9-bc3c-e8c4b535e6b7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_longitudinal_ratio

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
theorem _root_.solution {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => (supportDegree b n : ℝ) / (n : ℝ))
      atTop (nhds b) := by
  simpa [supportDegree] using
    MetricCodes.Hamming.tendsto_longitudinal_ratio hb
end MetricCodes.Johnson.Asymptotics
