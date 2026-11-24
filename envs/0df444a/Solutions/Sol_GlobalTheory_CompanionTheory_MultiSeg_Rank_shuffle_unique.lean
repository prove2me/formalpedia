-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.shuffle_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:06.834336+00:00
-- url     : https://prove2.me/submissions/e7852caf-9d08-4fe1-9869-c9a322d5472a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_interleave_perm
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_shuffle_mem

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
theorem _root_.solution {us : List (List T)} {w : List T} (h : Shuffle us w) (hw : w.Nodup)
    (y : T) : us.countP (fun x => decide (y ∈ x)) ≤ 1 := by
  revert hw
  induction h with
  | nil => intro _; simp
  | @cons u us v w hS hI ih =>
    intro hw
    have hnd : (u ++ v).Nodup := (interleave_perm hI).nodup_iff.2 hw
    have hvn : v.Nodup := hnd.of_append_right
    rw [List.countP_cons]
    by_cases hyu : y ∈ u
    · have h0 : us.countP (fun x => decide (y ∈ x)) = 0 := by
        rw [List.countP_eq_zero]
        intro x hx hyx
        exact List.disjoint_of_nodup_append hnd hyu (shuffle_mem hS hx (of_decide_eq_true hyx))
      simp [h0, hyu]
    · simpa [hyu] using ih hvn
end GlobalTheory.CompanionTheory.MultiSeg.Rank
