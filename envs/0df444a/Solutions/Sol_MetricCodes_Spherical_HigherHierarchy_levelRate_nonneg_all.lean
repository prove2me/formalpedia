-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_nonneg_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/90e14783-c34f-47f1-8ade-27816b27c881

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_nonneg_of_nonempty

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
theorem _root_.solution (r : ℕ) (s : ℝ) : 0 ≤ levelRate r s := by
  by_cases hnonempty : (levelRateSet r s).Nonempty
  · exact levelRate_nonneg_of_nonempty hnonempty
  · have hempty : levelRateSet r s = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp [levelRate, hempty]
end MetricCodes.Spherical.HigherHierarchy
