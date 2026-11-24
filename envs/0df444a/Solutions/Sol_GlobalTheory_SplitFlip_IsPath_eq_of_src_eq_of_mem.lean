-- Prove2me | solution 1 for GlobalTheory.SplitFlip.IsPath.eq_of_src_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:14.234935+00:00
-- url     : https://prove2.me/submissions/1f0fd811-9954-41d4-8052-b2c99d58c3c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
import Theorems.Thm_GlobalTheory_SplitFlip_IsPath_pairwise_lt_source_index_difference_along_path

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
theorem _root_.solution {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : a.src = b.src) : a = b :=
  List.inj_on_of_nodup_map hγ.pairwise_lt_source_index_difference_along_path.nodup ha hb (by simp [h])
end IsPath
end GlobalTheory.SplitFlip
