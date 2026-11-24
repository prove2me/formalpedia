-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.conjT_gramQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:40.892617+00:00
-- url     : https://prove2.me/submissions/754aee65-be0a-471b-8874-3fab34c56ab8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_neg
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_zero
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_fromBlocks
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_antiJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] {σ : L →+* L}
namespace GlobalTheory.FrameCompletion
theorem _root_.solution {n : ℕ} : cT σ (gramQ L n) = gramQ L n := by
  rw [gramQ, conjT_fromBlocks, conjT_antiJ, conjT_zero, conjT_neg, conjT_antiJ]
end GlobalTheory.FrameCompletion
