-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sphericalCodeRate_le_localizedHierarchyInf_of_compactification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/2a235960-f5e5-4be9-839c-efc91fb5002d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_closedHierarchyVariationalRate_eq_hierarchyVariationalRate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sphericalCodeRate_le_closedHierarchyVariationalRate_of_code_bound
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification

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
    (hcompact : GenuineCompactifiedHierarchyTransfer)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    sphericalCodeRate s ≤
      sInf (Set.range fun r : ℕ =>
        MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s) := by
  calc
    sphericalCodeRate s ≤ closedHierarchyVariationalRate s :=
      sphericalCodeRate_le_closedHierarchyVariationalRate_of_code_bound
        hcode hs hs'
    _ = hierarchyVariationalRate s :=
      closedHierarchyVariationalRate_eq_hierarchyVariationalRate hs hs'
    _ ≤ sInf (Set.range fun r : ℕ =>
          MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
            (levelRate r) s) :=
      hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification
        hcompact hs hs'
end MetricCodes.Spherical.HigherHierarchy
