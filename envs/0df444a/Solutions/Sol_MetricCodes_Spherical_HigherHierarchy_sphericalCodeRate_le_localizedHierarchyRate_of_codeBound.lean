-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sphericalCodeRate_le_localizedHierarchyRate_of_codeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/fda5f08f-20e8-4e9c-a41c-3bfc14cca710

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sphericalCodeRate_le_localizedHierarchyInf

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
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    sphericalCodeRate s ≤ localizedHierarchyRate s := by
  simpa [localizedHierarchyRate, localizedLevelRate] using
    (sphericalCodeRate_le_localizedHierarchyInf hcode hs hs')
end MetricCodes.Spherical.HigherHierarchy
