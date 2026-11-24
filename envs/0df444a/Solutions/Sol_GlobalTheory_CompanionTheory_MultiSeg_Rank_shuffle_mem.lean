-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.shuffle_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:36.550993+00:00
-- url     : https://prove2.me/submissions/7a88ee7a-2eac-4eff-bfc3-32c09c553719

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_interleave_mem

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
theorem _root_.solution {us : List (List T)} {w : List T} (h : Shuffle us w) {x : List T}
    (hx : x ∈ us) {y : T} (hy : y ∈ x) : y ∈ w := by
  revert hx
  induction h with
  | nil => intro hx; simp at hx
  | cons hS hI ih =>
    intro hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact (interleave_mem hI).2 (Or.inl hy)
    · exact (interleave_mem hI).2 (Or.inr (ih hx'))
end GlobalTheory.CompanionTheory.MultiSeg.Rank
