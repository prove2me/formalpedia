-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.length_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:46:59.448011+00:00
-- url     : https://prove2.me/submissions/5d28e149-57e4-4921-8e85-a9fcccaa1a33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_length_eq_ker_add_range

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
theorem _root_.solution {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (h : Function.Exact f g) :
    Module.length A N₂ =
      Module.length A (LinearMap.range f) + Module.length A (LinearMap.range g) := by
  rw [length_eq_ker_add_range g, LinearMap.exact_iff.mp h]
end GlobalTheory.ScalarSnakeLength
