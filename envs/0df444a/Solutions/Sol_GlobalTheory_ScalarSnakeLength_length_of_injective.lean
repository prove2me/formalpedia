-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.length_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:45.85637+00:00
-- url     : https://prove2.me/submissions/7607e547-eebb-4112-9472-f31af767fe74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ScalarSnakeLength
variable {A : Type} [CommRing A]
namespace GlobalTheory.ScalarSnakeLength
theorem _root_.solution {N₁ N₂ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (f : N₁ →ₗ[A] N₂) (hf : Function.Injective f) :
    Module.length A N₁ = Module.length A (LinearMap.range f) :=
  (LinearEquiv.ofInjective f hf).length_eq
end GlobalTheory.ScalarSnakeLength
