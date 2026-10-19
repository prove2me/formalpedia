-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_shellWeight_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/9bd7a140-565b-4fe6-80b6-eaaaa0fd0ad0

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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (shellWeight a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa [shellWeight] using
    MetricCodes.Hamming.tendsto_longitudinal_ratio ha
end MetricCodes.Johnson.Asymptotics
