-- Prove2me | solution 1 for GlobalTheory.UnramSub.range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:36:01.268445+00:00
-- url     : https://prove2.me/submissions/26156506-1ab1-4295-a327-01a19d075c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.UnramSub
variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}
namespace GlobalTheory.UnramSub
theorem _root_.solution [IsDomain V] [IsDiscreteValuationRing V] (hi : Function.Injective i) : UnramSub i i.range := by
  let e : V ≃+* i.range := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hi)
  exact ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, e.toRingHom, fun v => rfl,
    fun π hπ => hπ.map e⟩
end GlobalTheory.UnramSub
