-- Prove2me | solution 1 for GlobalTheory.SplitFlip.IsPath.pairwise_vertexDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:57.068607+00:00
-- url     : https://prove2.me/submissions/be80bb60-eb3e-444f-813e-8afd702334cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
import Theorems.Thm_GlobalTheory_SplitFlip_vertexDiff_tgt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip
namespace GlobalTheory.SplitFlip
namespace IsPath
theorem _root_.solution : ∀ {γ : List Edge}, IsPath γ →
    γ.Pairwise fun a b => vertexDiff a.src < vertexDiff b.src
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    unfold IsPath at h
    rw [List.isChain_cons_cons] at h
    have ih := solution (γ := b :: t) h.2
    have hab : vertexDiff a.src < vertexDiff b.src := by
      rw [← h.1, vertexDiff_tgt]; omega
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact hab.trans (List.rel_of_pairwise_cons ih hc)
end IsPath
end GlobalTheory.SplitFlip
