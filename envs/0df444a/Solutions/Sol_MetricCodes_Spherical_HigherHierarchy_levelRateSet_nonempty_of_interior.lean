-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRateSet_nonempty_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/7e0938dd-ced7-4322-af2c-0fe39e03f735

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_nextLevel_feasible_lt
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_zero_nonempty_of_interior

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
theorem _root_.solution (r : ℕ) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    (levelRateSet r s).Nonempty := by
  induction r with
  | zero =>
      exact levelRateSet_zero_nonempty_of_interior hs hs'
  | succ r ih =>
      obtain ⟨_, a, b, h, hgap, rfl⟩ := ih
      obtain ⟨A, B, hAB, hgapAB, _⟩ :=
        exists_nextLevel_feasible_lt hs h hgap
      exact ⟨Phi A B, A, B, hAB, hgapAB, rfl⟩
end MetricCodes.Spherical.HigherHierarchy
