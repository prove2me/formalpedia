-- Prove2me | solution 1 for GlobalTheory.LevDesc.autMat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:20.719345+00:00
-- url     : https://prove2.me/submissions/ef64dcaf-4b3a-450b-8d6f-56460970a300

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_autMat_mulVec

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
theorem _root_.solution : Function.Injective (autMat (O := O) e) := fun γ δ h =>
  LinearEquiv.ext fun x => e.injective (by rw [← autMat_mulVec, ← autMat_mulVec, h])
end GlobalTheory.LevDesc
