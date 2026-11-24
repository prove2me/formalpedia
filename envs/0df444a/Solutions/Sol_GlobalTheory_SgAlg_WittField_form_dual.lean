-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.form_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:36.283142+00:00
-- url     : https://prove2.me/submissions/a449ab58-49f2-4af9-b498-516d44cfb29b

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
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hdet : IsUnit J.det) (m v : Fin n → E) :
    form σ J v (fun k => σ ((m ᵥ* J⁻¹) k)) = m ⬝ᵥ v := by
  unfold form
  simp only [hσ]
  rw [show (fun k => (m ᵥ* J⁻¹) k) = m ᵥ* J⁻¹ from rfl, ← dotProduct_mulVec, mulVec_mulVec,
    nonsing_inv_mul J hdet, one_mulVec]
end GlobalTheory.SgAlg.WittField
