-- Prove2me | solution 1 for GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:55.040376+00:00
-- url     : https://prove2.me/submissions/1b03d7ba-d807-4340-91f0-43a01b7dce45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixOneParameterGroupEqExpOfContinuous
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixOneParameterGroupEqExpOfContinuousStatement
import Theorems.Thm_GlobalTheory_OneParamMatrix_eq_exp_of_continuous_oneParameter


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
theorem _root_.solution : ∀ {n : Type} [Fintype n] [DecidableEq n] (N : ℝ → Matrix n n ℂ), Continuous N → N 0 = 1 → (∀ s t, N (s + t) = N s * N t) → ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter | exact GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter | (intros; apply GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter <;> assumption)
end _root_.GlobalTheory.T
