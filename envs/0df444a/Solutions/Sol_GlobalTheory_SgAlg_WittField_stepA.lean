-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.stepA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:39:01.501662+00:00
-- url     : https://prove2.me/submissions/ccd656c4-77dd-4192-84cd-2d6f9e838a4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_sub_left
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_sub_right
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_conj
import Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_mulVec
import Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_qr
import Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_fix

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
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {a : ℕ} (y : Fin a → Fin n → E)
    (x x' : Fin n → E) (hy : ∀ i, form σ J (y i) x = form σ J (y i) x')
    (hxx : form σ J x x = form σ J x' x') (hc : form σ J x (x - x') ≠ 0) :
    ∃ g, IsUn σ J g ∧ (∀ i, g *ᵥ y i = y i) ∧ g *ᵥ x = x' := by
  set c := form σ J x (x - x') with hcdef
  have hσc : σ c ≠ 0 := by
    intro h; apply hc; rw [← hσ c, h, map_zero]
  have hN : form σ J (x - x') (x - x') = c + σ c := by
    rw [hcdef, ← form_conj hσ hJ]
    simp only [form_sub_left, form_sub_right]
    linear_combination (-1 : E) * hxx
  refine ⟨qr σ J (x - x') c⁻¹, isUn_qr hσ hJ _ _ ?_, fun i => qr_fix _ _ _ ?_, ?_⟩
  · rw [map_inv₀, hN]; field_simp; ring
  · rw [form_sub_right, hy i, sub_self]
  · rw [qr_mulVec, ← hcdef, inv_mul_cancel₀ hc, one_smul]; abel
end GlobalTheory.SgAlg.WittField
