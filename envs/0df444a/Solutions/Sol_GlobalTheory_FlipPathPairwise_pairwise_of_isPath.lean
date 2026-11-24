-- Prove2me | solution 1 for GlobalTheory.FlipPathPairwise.pairwise_of_isPath
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:47:03.535313+00:00
-- url     : https://prove2.me/submissions/94e0d77a-2e94-4a6c-99b6-76f8fc40d574

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSplitThetaGridPathFlipGridPathAtSquare
import Theorems.Thm_GlobalTheory_FlipPathPairwise_srcDiff_of_join

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
open GlobalTheory GlobalTheory.FlipPathPairwise
namespace GlobalTheory.FlipPathPairwise
theorem _root_.solution {γ : List Edge} (h : IsPath γ) :
    γ.Pairwise fun a b => srcDiff a < srcDiff b := by
  have h' : γ.IsChain fun a b => srcDiff a < srcDiff b :=
    List.IsChain.imp (fun a b hab => by rw [srcDiff_of_join hab]; omega) h
  haveI : Trans (fun a b : Edge => srcDiff a < srcDiff b) (fun a b => srcDiff a < srcDiff b)
      (fun a b => srcDiff a < srcDiff b) := ⟨fun h1 h2 => lt_trans h1 h2⟩
  exact h'.pairwise
end GlobalTheory.FlipPathPairwise
