-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.rank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:06.318437+00:00
-- url     : https://prove2.me/submissions/ad9bc80e-4d1f-446f-a859-353acb216a69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_dec_eq_word
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_count_le

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
theorem _root_.solution (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {L : List (ASeg T)} {n : Multiset (ASeg T)}
    (hL : AOrdered s L) (hn : InSh s n (wt s L)) (u : T) (d : ℕ) :
    rank s n u d ≤ rank s (L : Multiset (ASeg T)) u d := by
  obtain ⟨L', hL', hsh⟩ := hn
  subst hL'
  unfold rank
  rw [Multiset.coe_countP, Multiset.coe_countP]
  have hB : L.reverse.Pairwise (fun a b => ¬ APrecedes s b a) := List.pairwise_reverse.2 hL
  have h := count_le s hs hp L.reverse hB (L'.map (ASeg.dec s)) hsh
    (fun x hx => by
      obtain ⟨Δ, _, rfl⟩ := List.mem_map.1 hx
      exact ⟨Δ.start, Δ.len, dec_eq_word s Δ⟩) u d
  rw [List.countP_map, List.countP_reverse] at h
  exact h
end GlobalTheory.CompanionTheory.MultiSeg.Rank
