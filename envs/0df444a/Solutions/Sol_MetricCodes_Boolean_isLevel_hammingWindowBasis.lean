-- Prove2me | solution 1 for MetricCodes.Boolean.isLevel_hammingWindowBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/d7a64079-c738-47a4-a289-ddb4cc4d1ab9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution (n k L : ℕ)
    (T : HammingWindowIndex n k L) :
    IsLevel (k + T.1.val) (hammingWindowBasis n k L T) := by
  classical
  intro S hS
  unfold hammingWindowBasis
  split_ifs with heq
  · subst S
    exact False.elim (hS T.2.property)
  · rfl
end MetricCodes.Boolean
