-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.cT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:34.050093+00:00
-- url     : https://prove2.me/submissions/8729bb22-a19f-4496-870d-56ac789eae22

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
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) E) : cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT
  rw [Matrix.map_mul, transpose_mul]
end GlobalTheory.SgAlg.WittField
