-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sphericalCodeRate_le_localizedHierarchyInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/3361882a-a1f9-4580-8758-1686177e82f9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sphericalCodeRate_le_localizedHierarchyInf_of_compactification
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_genuineCompactifiedHierarchyTransfer

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
set_option autoImplicit false
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    sphericalCodeRate s ≤
      sInf (Set.range fun r : ℕ =>
        MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s) :=
  sphericalCodeRate_le_localizedHierarchyInf_of_compactification
    hcode genuineCompactifiedHierarchyTransfer hs hs'
end MetricCodes.Spherical.HigherHierarchy
