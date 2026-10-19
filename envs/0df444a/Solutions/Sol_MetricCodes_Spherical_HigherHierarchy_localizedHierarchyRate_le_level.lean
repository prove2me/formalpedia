-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedHierarchyRate_le_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/86875499-9a25-4569-ac38-f0bab198351d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedLevelRate_nonneg

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
theorem _root_.solution {r : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hs' : s < 1) :
    localizedHierarchyRate s ≤ localizedLevelRate r s := by
  unfold localizedHierarchyRate
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact localizedLevelRate_nonneg hs hs'
  · exact ⟨r, rfl⟩
end MetricCodes.Spherical.HigherHierarchy
