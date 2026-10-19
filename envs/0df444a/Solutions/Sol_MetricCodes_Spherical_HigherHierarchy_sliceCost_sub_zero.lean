-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sliceCost_sub_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/2175afe7-53cf-45a2-88c9-8e992b26ae38

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {s t : ℝ}
    (hs : s < 1) (ht : t < 1) :
    MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t -
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0 =
      (1 / 2 : ℝ) * Real.logb 2 (1 - t) := by
  have hs' : 1 - s ≠ 0 := by linarith
  have ht' : 1 - t ≠ 0 := by linarith
  unfold MetricCodes.Spherical.SidelnikovLocalization.sliceCost
  norm_num only [sub_zero]
  rw [Real.logb_div ht' hs',
    Real.logb_div (by norm_num : (1 : ℝ) ≠ 0) hs']
  simp
  ring
end MetricCodes.Spherical.HigherHierarchy
