-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonJ_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/2ee2a0da-a68e-481b-a726-f3284f0f9914

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_dimension_ratio
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_terminalIndex_ratio

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
      (fun n : ℕ =>
        MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredDegree u / 2)) := by
  have hspin := tendsto_dimension_ratio.div_const 2
  have hmain := hspin.sub (tendsto_terminalIndex_ratio hu r)
  have hcenter : (1 : ℝ) / 2 - u =
      MetricCodes.Johnson.centeredDegree u / 2 := by
    unfold MetricCodes.Johnson.centeredDegree
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ
  ring
end MetricCodes.Johnson.SpectralAsymptotics
