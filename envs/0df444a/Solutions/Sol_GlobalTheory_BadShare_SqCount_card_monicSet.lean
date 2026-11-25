-- Prove2me | solution 1 for GlobalTheory.BadShare.SqCount.card_monicSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:46:21.505044+00:00
-- url     : https://prove2.me/submissions/ac03329d-b5a0-490e-bde1-0940db579fcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.SqCount
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare.SqCount
theorem _root_.solution (N : ℕ) : (monicSet g N).card = g ^ N := by
  unfold monicSet
  rw [Finset.card_image_of_injective]
  · simp [ZMod.card]
  · intro c d h
    have h' := add_left_cancel h
    funext i
    have := congrArg (fun p => coeff p i) h'
    simpa [finset_sum_coeff, coeff_X_pow, Fin.val_inj] using this
end GlobalTheory.BadShare.SqCount
