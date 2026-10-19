-- Prove2me | solution 1 for MetricCodes.MRRW.tendsto_interiorWeight_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/921dcfdd-625f-445c-aa93-cc25f5443bac

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution (a u : ℝ) :
    Tendsto (interiorWeight a u) (𝓝[>] 0) (𝓝 a) := by
  have hcontinuous : Continuous (interiorWeight a u) := by
    unfold interiorWeight
    fun_prop
  simpa using hcontinuous.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
end MetricCodes.MRRW
