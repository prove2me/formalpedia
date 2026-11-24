-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.qr_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:13:10.616813+00:00
-- url     : https://prove2.me/submissions/1b517bd0-26c8-4fef-b454-bece59ea1a28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_sub_left
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_smul_left
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_sub_right
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_smul_right
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_conj
import Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_mulVec

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
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (u : Fin n → E) (l : E)
    (hl : l * σ l * form σ J u u = l + σ l) (v w : Fin n → E) :
    form σ J (qr σ J u l *ᵥ v) (qr σ J u l *ᵥ w) = form σ J v w := by
  rw [qr_mulVec, qr_mulVec]
  simp only [form_sub_left, form_sub_right, form_smul_left, form_smul_right, map_mul]
  rw [form_conj hσ hJ w u]
  linear_combination (form σ J v u * σ (form σ J w u)) * hl
end GlobalTheory.SgAlg.WittField
