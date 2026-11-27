-- Prove2me | solution 1 for GlobalTheory.T.trace_sum_single_comp_proj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:04:14.356951+00:00
-- url     : https://prove2.me/submissions/8731222f-3e77-4ef1-9fef-86b9d6abcecb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TraceMatrixPiOperator
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TraceMatrixPiOperatorStatement
import Theorems.Thm_GlobalTheory_trace_matrix_pi_operator


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
theorem _root_.solution : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  first | exact @GlobalTheory.trace_matrix_pi_operator | exact GlobalTheory.trace_matrix_pi_operator | (intros; apply GlobalTheory.trace_matrix_pi_operator <;> assumption)
end _root_.GlobalTheory.T
