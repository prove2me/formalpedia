-- Prove2me | solution 1 for GlobalTheory.SplitFlip.PathSplit.pairwise_of_isPath
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:07:56.560798+00:00
-- url     : https://prove2.me/submissions/9be2d593-ac24-4932-91a7-987733440d84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlipGridPathAtSquareSplit
import Theorems.Thm_GlobalTheory_SplitFlip_PathSplit_vdiff_tgt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.PathSplit
open GlobalTheory.SplitFlip
namespace GlobalTheory.SplitFlip.PathSplit
theorem _root_.solution : ∀ {γ : List Edge}, IsPath γ → γ.Pairwise (fun a b => vdiff a.src < vdiff b.src)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    unfold IsPath at h
    rw [List.isChain_cons_cons] at h
    have ih := solution (γ := b :: l) h.2
    have hab : vdiff a.src < vdiff b.src := by
      have := vdiff_tgt a; rw [h.1] at this; omega
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact hab.trans (List.rel_of_pairwise_cons ih hc)
end GlobalTheory.SplitFlip.PathSplit
