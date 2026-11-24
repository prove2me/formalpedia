-- Prove2me | solution 1 for GlobalTheory.kernel_cokernel_length_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:21.367986+00:00
-- url     : https://prove2.me/submissions/63167b8c-a7cf-4e8b-a19a-365b614f01f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  intro A _ _ a b ha hb
  refine ⟨(GlobalTheory.ASwap.kerEquiv a b ha hb).length_eq, ?_⟩
  exact ((GlobalTheory.ASwap.cokerEquiv a b).trans ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans
    (GlobalTheory.ASwap.cokerEquiv b a).symm)).length_eq
end GlobalTheory
