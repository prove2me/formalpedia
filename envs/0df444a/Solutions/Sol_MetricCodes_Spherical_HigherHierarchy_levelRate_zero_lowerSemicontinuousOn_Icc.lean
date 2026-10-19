-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_zero_lowerSemicontinuousOn_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/d688afaf-37d9-47b2-81d5-eb70781cf2e0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_zero_continuousOn_Icc

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s : ℝ} (hs : s < 1) :
    LowerSemicontinuousOn (levelRate 0) (Set.Icc (0 : ℝ) s) :=
  (levelRate_zero_continuousOn_Icc hs).lowerSemicontinuousOn
end MetricCodes.Spherical.HigherHierarchy
