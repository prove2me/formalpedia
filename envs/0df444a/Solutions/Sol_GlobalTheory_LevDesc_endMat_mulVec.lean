-- Prove2me | solution 1 for GlobalTheory.LevDesc.endMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:28.146921+00:00
-- url     : https://prove2.me/submissions/f592ac7f-e3c3-4595-912a-f40e85b00380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

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
theorem _root_.solution (γ : Module.End O M) (x : M) : (endMat e γ).mulVec (e x) = e (γ x) := by
  simp [endMat, LinearMap.toMatrix'_mulVec]
end GlobalTheory.LevDesc
