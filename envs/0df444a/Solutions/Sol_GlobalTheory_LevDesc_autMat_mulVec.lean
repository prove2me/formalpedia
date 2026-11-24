-- Prove2me | solution 1 for GlobalTheory.LevDesc.autMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:57:11.638485+00:00
-- url     : https://prove2.me/submissions/73ccaaa3-71b4-4688-8b7c-3b4a56b9720c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_endMat_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] {r p : ℕ} (e : M ≃+ (Fin r → ZMod p))
namespace GlobalTheory.LevDesc
theorem _root_.solution (γ : M ≃ₗ[O] M) (x : M) :
    (autMat e γ : Matrix (Fin r) (Fin r) (ZMod p)).mulVec (e x) = e (γ x) := endMat_mulVec e _ x
end GlobalTheory.LevDesc
