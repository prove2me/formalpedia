-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.herm_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:37.088742+00:00
-- url     : https://prove2.me/submissions/a60aa85f-e200-486e-b83d-cc21612c3e4b

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
theorem _root_.solution (hJ : cT σ J = J) (i j : Fin n) : σ (J j i) = J i j := by
  have := congrFun (congrFun hJ i) j
  simpa [cT] using this
end GlobalTheory.SgAlg.WittField
