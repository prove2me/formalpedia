-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.form_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:35.463801+00:00
-- url     : https://prove2.me/submissions/08efe3ec-357e-4d16-8033-512b64b52dc3

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
theorem _root_.solution (v w w' : Fin n → E) : form σ J v (w + w') = form σ J v w + form σ J v w' := by
  simp only [form, Pi.add_apply, map_add]
  rw [show (fun i => σ (w i) + σ (w' i)) = (fun i => σ (w i)) + (fun i => σ (w' i)) from rfl, add_dotProduct]
end GlobalTheory.SgAlg.WittField
