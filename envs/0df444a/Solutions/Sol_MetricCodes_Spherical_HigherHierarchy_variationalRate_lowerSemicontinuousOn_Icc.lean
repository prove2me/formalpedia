-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.variationalRate_lowerSemicontinuousOn_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/80ac9017-2c84-4c0c-80fb-7ffd87ceb3e8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_entropy_sub_boundaryDegree_of_tendsto
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_variationalRate_lowerSemicontinuousOn_Icc_of_jointEscape

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Set Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    LowerSemicontinuousOn MetricCodes.Spherical.variationalRate
      (Set.Icc (0 : ℝ) s) := by
  apply variationalRate_lowerSemicontinuousOn_Icc_of_jointEscape hs hs'
  intro u a t ht ht' hu ha
  simpa [oneRowBoundaryObjective] using
    (CompactificationEntropy.tendsto_entropy_sub_boundaryDegree_of_tendsto
      ht ht' hu ha)
end MetricCodes.Spherical.HigherHierarchy
