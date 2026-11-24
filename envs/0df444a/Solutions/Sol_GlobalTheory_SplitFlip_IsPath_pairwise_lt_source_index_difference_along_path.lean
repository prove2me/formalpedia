-- Prove2me | solution 1 for GlobalTheory.SplitFlip.IsPath.pairwise_lt_source_index_difference_along_path
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:07:42.941802+00:00
-- url     : https://prove2.me/submissions/0616215c-ef8d-4f84-8c60-36b8e05270da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
import Theorems.Thm_GlobalTheory_SplitFlip_pathInnerDiff_tgt

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
theorem _root_.solution {γ : List Edge} (hγ : IsPath γ) :
    (γ.map fun e => pathInnerDiff e.src).Pairwise (· < ·) := by
  have h : (γ.map fun e => pathInnerDiff e.src).IsChain (· < ·) :=
    List.isChain_map_of_isChain _ (R := fun a b : Edge => a.tgt = b.src) (fun a b (hab : a.tgt = b.src) => by
      show pathInnerDiff a.src < pathInnerDiff b.src
      rw [← hab, pathInnerDiff_tgt]; omega) (by unfold IsPath at hγ; exact hγ)
  exact h.pairwise
end IsPath
end GlobalTheory.SplitFlip
