-- Prove2me | solution 1 for GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:19:04.223807+00:00
-- url     : https://prove2.me/submissions/07d29986-1f11-45e8-9e5f-023ce559ac44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Theorems.Thm_GlobalTheory_kernel_cokernel_length_swap


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  first | exact @GlobalTheory.kernel_cokernel_length_swap | exact GlobalTheory.kernel_cokernel_length_swap | (intros; apply GlobalTheory.kernel_cokernel_length_swap <;> assumption)
end _root_.GlobalTheory.T
