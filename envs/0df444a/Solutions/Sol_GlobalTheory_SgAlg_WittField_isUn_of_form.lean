-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.isUn_of_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:12:26.45171+00:00
-- url     : https://prove2.me/submissions/21b4eb59-e866-46ec-b6f1-1adb06951e59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_mulVec
import Theorems.Thm_GlobalTheory_SgAlg_WittField_single_entry

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
theorem _root_.solution {g : Matrix (Fin n) (Fin n) E}
    (h : ∀ v w, form σ J (g *ᵥ v) (g *ᵥ w) = form σ J v w) : IsUn σ J g := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [form_mulVec] at this
  unfold form at this
  rwa [single_entry, single_entry] at this
end GlobalTheory.SgAlg.WittField
