-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_zero_continuousOn_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/8e0c6b2f-2a81-4ece-bbc3-b7adac335e58

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_zero_eq_classical
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_classicalHierarchyProfile_continuousOn_Icc

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
    ContinuousOn (levelRate 0) (Set.Icc (0 : ℝ) s) := by
  apply (classicalHierarchyProfile_continuousOn_Icc hs).congr
  intro t ht
  exact levelRate_zero_eq_classical ht.1
    (lt_of_le_of_lt ht.2 hs)
end MetricCodes.Spherical.HigherHierarchy
