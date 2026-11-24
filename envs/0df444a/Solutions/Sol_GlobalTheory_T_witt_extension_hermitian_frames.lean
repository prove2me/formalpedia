-- Prove2me | solution 1 for GlobalTheory.T.witt_extension_hermitian_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:39.51533+00:00
-- url     : https://prove2.me/submissions/b480fc26-38d8-439e-a251-85c528502e77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFramesStatement
import Theorems.Thm_GlobalTheory_SgAlg_witt_free_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] (σ : E →+* E), IsQA σ → ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  first | exact @GlobalTheory.SgAlg.witt_free_field | exact GlobalTheory.SgAlg.witt_free_field | (intros; apply GlobalTheory.SgAlg.witt_free_field <;> assumption)
end _root_.GlobalTheory.T
