-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.form_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:58.745587+00:00
-- url     : https://prove2.me/submissions/34a363fc-0d6d-423f-839a-a995d993f6b4

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
theorem _root_.solution (v v' w : Fin n → E) : form σ J (v + v') w = form σ J v w + form σ J v' w := by
  simp [form, mulVec_add, dotProduct_add]
end GlobalTheory.SgAlg.WittField
