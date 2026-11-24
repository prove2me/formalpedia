-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.isUn_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:31.3688+00:00
-- url     : https://prove2.me/submissions/3b9698da-59d8-4dee-a4b7-94a0a820da35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_mulVec

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
theorem _root_.solution {g : Matrix (Fin n) (Fin n) E} (hg : IsUn σ J g) (v w : Fin n → E) :
    form σ J (g *ᵥ v) (g *ᵥ w) = form σ J v w := by
  rw [form_mulVec, hg]; rfl
end GlobalTheory.SgAlg.WittField
