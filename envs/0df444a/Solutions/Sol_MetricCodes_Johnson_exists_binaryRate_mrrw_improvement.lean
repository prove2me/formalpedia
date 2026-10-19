-- Prove2me | solution 1 for MetricCodes.Johnson.exists_binaryRate_mrrw_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/5b6839cd-ed14-46c4-9dff-9eba407aff17

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_strict_mrrw2
import Theorems.Thm_MetricCodes_Johnson_binaryRate_le_combinedVariationalRate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson
theorem _root_.solution
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    ∃ e : ℝ, 0 < e ∧ MetricCodes.Hamming.binaryRate d ≤ mrrwRate d - e := by
  refine ⟨mrrwRate d - combinedVariationalRate d, ?_, ?_⟩
  · exact sub_pos.mpr (MetricCodes.MRRW.strict_mrrw2 hd hdhalf)
  · linarith [binaryRate_le_combinedVariationalRate hd hdhalf]
end MetricCodes.Johnson
