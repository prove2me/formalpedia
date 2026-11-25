-- Prove2me | solution 1 for GlobalTheory.T.eventually_rpow_log_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:19:25.809175+00:00
-- url     : https://prove2.me/submissions/3946ab9a-8a51-499d-8fa7-4ff70438b11d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiveElementaryInequalitiesEventually
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiveElementaryInequalitiesEventuallyStatement
import Theorems.Thm_GlobalTheory_five_elementary_inequalities_eventually


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop, x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧ 11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧ 2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧ 44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  first | exact @GlobalTheory.five_elementary_inequalities_eventually | exact GlobalTheory.five_elementary_inequalities_eventually | (intros; apply GlobalTheory.five_elementary_inequalities_eventually <;> assumption)
end _root_.GlobalTheory.T
