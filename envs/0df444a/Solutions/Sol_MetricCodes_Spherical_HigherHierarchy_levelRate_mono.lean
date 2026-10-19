-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/de648926-b1c2-4995-97c1-918ad4e8b954

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_bddBelow
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_nonempty_of_interior

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
theorem _root_.solution {r : ℕ} {s t : ℝ}
    (hst : s ≤ t) (ht : 0 < t) (ht' : t < 1) :
    levelRate r s ≤ levelRate r t := by
  unfold levelRate
  apply csInf_le_csInf (levelRateSet_bddBelow r s)
    (levelRateSet_nonempty_of_interior r ht ht')
  rintro _ ⟨a, b, h, hgap, hPhi⟩
  exact ⟨a, b, h, hst.trans_lt hgap, hPhi⟩
end MetricCodes.Spherical.HigherHierarchy
