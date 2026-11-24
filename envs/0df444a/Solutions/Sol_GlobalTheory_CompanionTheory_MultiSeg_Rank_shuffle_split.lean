-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.shuffle_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:14:09.335808+00:00
-- url     : https://prove2.me/submissions/48f997de-f3d6-4f00-a720-804d0216af6f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_interleave_split

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
theorem _root_.solution : ∀ (us : List (List T)) (D w' : List T), Shuffle us (D ++ w') →
    ∃ P : List (List T × List T), P.map (fun p => p.1 ++ p.2) = us ∧
      Shuffle (P.map Prod.fst) D ∧ Shuffle (P.map Prod.snd) w' := by
  intro us
  induction us with
  | nil =>
    intro D w' h
    generalize hx : D ++ w' = x at h
    cases h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hx
    exact ⟨[], rfl, Shuffle.nil, Shuffle.nil⟩
  | cons u us ih =>
    intro D w' h
    generalize hx : D ++ w' = x at h
    cases h with
    | cons hS hI =>
      subst hx
      obtain ⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩ := interleave_split D w' _ _ hI
      obtain ⟨P, hP, hP1, hP2⟩ := ih _ _ hS
      exact ⟨(u1, u2) :: P, by simp [hP], Shuffle.cons hP1 h1, Shuffle.cons hP2 h2⟩
end GlobalTheory.CompanionTheory.MultiSeg.Rank
