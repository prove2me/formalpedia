-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sliceCost_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/0c038686-c4c4-4e56-89be-b9452573eb90

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
theorem _root_.solution {s : ℝ} (hs : s < 1) :
    ContinuousOn
      (MetricCodes.Spherical.SidelnikovLocalization.sliceCost s)
      (Set.Icc (0 : ℝ) s) := by
  intro t ht
  have harg : (1 - t) / (1 - s) ≠ 0 := by
    exact (div_pos (by linarith [ht.2]) (by linarith)).ne'
  unfold MetricCodes.Spherical.SidelnikovLocalization.sliceCost Real.logb
  fun_prop
end MetricCodes.Spherical.HigherHierarchy
