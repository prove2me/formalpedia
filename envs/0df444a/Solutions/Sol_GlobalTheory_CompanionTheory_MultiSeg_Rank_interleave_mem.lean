-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.interleave_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:40.44188+00:00
-- url     : https://prove2.me/submissions/f61480ed-c74a-40da-b6da-57b7c062713f

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
theorem _root_.solution {u v w : List T} (h : Interleave u v w) {y : T} :
    y ∈ w ↔ y ∈ u ∨ y ∈ v := by
  induction h with
  | nil => simp
  | left _ ih => simp only [List.mem_cons, ih]; tauto
  | right _ ih => simp only [List.mem_cons, ih]; tauto
end GlobalTheory.CompanionTheory.MultiSeg.Rank
