-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.length_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:46.850775+00:00
-- url     : https://prove2.me/submissions/f3708518-9072-4a4c-b88c-aa437814612b

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
    [Module A N₂] (g : N₁ →ₗ[A] N₂) (hg : Function.Surjective g) :
    Module.length A (LinearMap.range g) = Module.length A N₂ := by
  rw [LinearMap.range_eq_top.mpr hg, Module.length_top]
end GlobalTheory.ScalarSnakeLength
