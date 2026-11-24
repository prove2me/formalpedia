-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.interleave_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:41.558531+00:00
-- url     : https://prove2.me/submissions/eb74ee97-6fde-4345-be20-9161181b7ecd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
open Classical
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MultiSeg GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}
namespace GlobalTheory.CompanionTheory.MultiSeg.Rank
theorem _root_.solution {u v w : List T} (h : Interleave u v w) : (u ++ v).Perm w := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact List.perm_middle.trans (ih.cons _)
end GlobalTheory.CompanionTheory.MultiSeg.Rank
