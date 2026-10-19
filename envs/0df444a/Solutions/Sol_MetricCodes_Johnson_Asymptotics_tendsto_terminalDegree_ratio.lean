-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_terminalDegree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/e85e510a-4874-467d-a567-4d8dda4d1c56

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
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => (terminalDegree u n : ℝ) / (n : ℝ))
      atTop (nhds u) := by
  simpa [terminalDegree] using
    MetricCodes.Hamming.tendsto_longitudinal_ratio hu
end MetricCodes.Johnson.Asymptotics
