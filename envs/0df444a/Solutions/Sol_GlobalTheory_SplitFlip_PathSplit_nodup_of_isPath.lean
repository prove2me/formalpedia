-- Prove2me | solution 1 for GlobalTheory.SplitFlip.PathSplit.nodup_of_isPath
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:14.962539+00:00
-- url     : https://prove2.me/submissions/ea50d9d5-3caf-454d-bbc7-5fd145567c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlipGridPathAtSquareSplit
import Theorems.Thm_GlobalTheory_SplitFlip_PathSplit_pairwise_of_isPath

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
theorem _root_.solution {γ : List Edge} (h : IsPath γ) : γ.Nodup :=
  (pairwise_of_isPath h).imp fun hab heq => by subst heq; exact lt_irrefl _ hab
end GlobalTheory.SplitFlip.PathSplit
