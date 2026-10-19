-- Prove2me | solution 1 for MetricCodes.sphericalCodeNumber_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/017c6add-8d1f-4641-a9ca-f1e97d914fce

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
noncomputable section
open scoped BigOperators InnerProductSpace
open MetricCodes
namespace MetricCodes
theorem _root_.solution {n : ℕ} {s : ℝ} {B : ℕ∞}
    (hB : ∀ C : SphericalCode n s, (C.points.card : ℕ∞) ≤ B) :
    sphericalCodeNumber n s ≤ B := by
  exact iSup_le hB
end MetricCodes
