-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.conj_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:34.753883+00:00
-- url     : https://prove2.me/submissions/293fed87-1cc8-4ada-9f6f-4987c521a7e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.SgAlg.WittField
theorem _root_.solution (B : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    (fun i => σ ((B *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* cT σ B := by
  funext k
  simp [mulVec, vecMul, dotProduct, cT, map_sum, map_mul, mul_comm]
end GlobalTheory.SgAlg.WittField
