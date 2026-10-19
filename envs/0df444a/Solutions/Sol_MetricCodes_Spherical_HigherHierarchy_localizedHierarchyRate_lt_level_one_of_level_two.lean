-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedHierarchyRate_lt_level_one_of_level_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/4809c9f1-820b-4e20-8de4-ac00325490f2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedHierarchyRate_le_level

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
    {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1)
    (hstrict : localizedLevelRate 2 s < localizedLevelRate 1 s) :
    localizedHierarchyRate s < localizedLevelRate 1 s :=
  (localizedHierarchyRate_le_level (r := 2) hs hs').trans_lt hstrict
end MetricCodes.Spherical.HigherHierarchy
