-- Prove2me | solution 1 for MetricCodes.Johnson.binaryRate_lt_mrrw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/968231f6-7bff-44aa-957f-51ed1c8fed04

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
    MetricCodes.Hamming.binaryRate d < mrrwRate d := by
  exact (binaryRate_le_combinedVariationalRate hd hdhalf).trans_lt
    (MetricCodes.MRRW.strict_mrrw2 hd hdhalf)
end MetricCodes.Johnson
