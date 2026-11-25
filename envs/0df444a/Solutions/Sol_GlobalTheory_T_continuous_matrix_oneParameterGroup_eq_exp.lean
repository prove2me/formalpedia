-- Prove2me | solution 1 for GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:39.519377+00:00
-- url     : https://prove2.me/submissions/381d3224-dc3b-4204-90e7-371a9ada552f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousMatrixOneParameterGroupEqExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousMatrixOneParameterGroupEqExpStatement
import Theorems.Thm_GlobalTheory_matrix_oneParamGroup_eq_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) → ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  first | exact @GlobalTheory.matrix_oneParamGroup_eq_exp | exact GlobalTheory.matrix_oneParamGroup_eq_exp | (intros; apply GlobalTheory.matrix_oneParamGroup_eq_exp <;> assumption)
end _root_.GlobalTheory.T
