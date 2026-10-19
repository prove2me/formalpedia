-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/016e53a2-696d-4bec-aa69-fb3a87c726bf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_localizedEnvelope_of_compactification

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
    (hcompact : GenuineCompactifiedHierarchyTransfer)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    hierarchyVariationalRate s ≤
      sInf (Set.range fun r : ℕ =>
        MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s) := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨r, rfl⟩
  exact hierarchyVariationalRate_le_localizedEnvelope_of_compactification
    hcompact hs hs'
end MetricCodes.Spherical.HigherHierarchy
