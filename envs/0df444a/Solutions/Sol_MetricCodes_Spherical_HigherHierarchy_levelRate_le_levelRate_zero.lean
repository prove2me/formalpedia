-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_le_levelRate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/21f757a4-e352-471b-9155-85ad10f391db

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_succ_le

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
    (hs : 0 < s) (hs' : s < 1) :
    levelRate r s ≤ levelRate 0 s := by
  induction r with
  | zero => exact le_rfl
  | succ r ih => exact (levelRate_succ_le hs hs').trans ih
end MetricCodes.Spherical.HigherHierarchy
