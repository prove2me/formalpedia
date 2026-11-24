-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.form_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:42.614729+00:00
-- url     : https://prove2.me/submissions/8ff3e482-b70d-487a-89a3-09ab266183d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_conj_mulVec

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
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    form σ J (A *ᵥ v) (B *ᵥ w) = (fun i => σ (w i)) ⬝ᵥ ((cT σ B * J * A) *ᵥ v) := by
  unfold form
  rw [conj_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
end GlobalTheory.SgAlg.WittField
