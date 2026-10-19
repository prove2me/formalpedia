-- Prove2me | solution 1 for MetricCodes.Johnson.binaryRate_le_combinedVariationalRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/16b46ce4-aa50-41c2-9548-a995fd3b6d9e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Rate_binaryRate_le_combinedVariationalRate_of_projectionGrams
import Theorems.Thm_MetricCodes_Johnson_eventually_projectionGram

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
    MetricCodes.Hamming.binaryRate d ≤ combinedVariationalRate d := by
  apply
    MetricCodes.Johnson.Rate.binaryRate_le_combinedVariationalRate_of_projectionGrams
      hd hdhalf
  intro a b g u hfeasible
  exact eventually_projectionGram hfeasible
end MetricCodes.Johnson
