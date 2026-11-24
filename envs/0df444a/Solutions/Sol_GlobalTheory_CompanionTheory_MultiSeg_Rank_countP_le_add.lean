-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.countP_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:39.448229+00:00
-- url     : https://prove2.me/submissions/50404bc2-7dff-4215-b640-a25f38a6cfbc

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
theorem _root_.solution {α : Type*} (l : List α) (p q r : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true ∨ r x = true) :
    l.countP p ≤ l.countP q + l.countP r := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    cases hpx : p x <;> cases hqx : q x <;> cases hrx : r x <;> simp [hpx, hqx, hrx] at hx ⊢ <;> omega
end GlobalTheory.CompanionTheory.MultiSeg.Rank
