-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.form_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:45.749332+00:00
-- url     : https://prove2.me/submissions/9792e8c8-7768-478b-ba04-3af1a26d472a

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
theorem _root_.solution (v v' w : Fin n → E) : form σ J (v - v') w = form σ J v w - form σ J v' w := by
  simp [form, mulVec_sub, dotProduct_sub]
end GlobalTheory.SgAlg.WittField
