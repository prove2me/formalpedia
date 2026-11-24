-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.form_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:46.125731+00:00
-- url     : https://prove2.me/submissions/85ef54a0-6681-487f-81a2-d839adf09f5e

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
theorem _root_.solution (v w w' : Fin n → E) : form σ J v (w - w') = form σ J v w - form σ J v w' := by
  simp only [form, Pi.sub_apply, map_sub]
  rw [show (fun i => σ (w i) - σ (w' i)) = (fun i => σ (w i)) - (fun i => σ (w' i)) from rfl, sub_dotProduct]
end GlobalTheory.SgAlg.WittField
