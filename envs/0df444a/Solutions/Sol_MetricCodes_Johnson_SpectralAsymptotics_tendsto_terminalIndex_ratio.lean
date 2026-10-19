-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_terminalIndex_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/4bd28ee5-0516-4d25-9e28-a85f1bfef223

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_terminal_degree_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    {u : ℝ} (hu : 0 < u) (r : ℕ) :
    Tendsto
      (fun n : ℕ => (terminalIndex u r n : ℝ) / (n : ℝ))
      atTop (nhds u) := by
  simpa [terminalIndex, terminalDegree] using
    MetricCodes.Hamming.tendsto_terminal_degree_ratio hu r
end MetricCodes.Johnson.SpectralAsymptotics
