-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.interleave_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:42.659609+00:00
-- url     : https://prove2.me/submissions/ddface2f-ea76-444f-904f-249f33fd44ea

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
theorem _root_.solution : ∀ (D w' u v : List T), Interleave u v (D ++ w') →
    ∃ u1 u2 v1 v2, u = u1 ++ u2 ∧ v = v1 ++ v2 ∧ Interleave u1 v1 D ∧ Interleave u2 v2 w' := by
  intro D w'
  induction D with
  | nil => intro u v h; exact ⟨[], u, [], v, rfl, rfl, Interleave.nil, h⟩
  | cons a D ih =>
    intro u v h
    rw [List.cons_append] at h
    cases h with
    | left h' =>
      obtain ⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩ := ih _ _ h'
      exact ⟨a :: u1, u2, v1, v2, rfl, rfl, Interleave.left h1, h2⟩
    | right h' =>
      obtain ⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩ := ih _ _ h'
      exact ⟨u1, u2, a :: v1, v2, rfl, rfl, Interleave.right h1, h2⟩
end GlobalTheory.CompanionTheory.MultiSeg.Rank
