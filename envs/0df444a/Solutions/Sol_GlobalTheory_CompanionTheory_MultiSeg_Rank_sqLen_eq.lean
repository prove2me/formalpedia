-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:26.199984+00:00
-- url     : https://prove2.me/submissions/f43c317d-4d73-4b3a-83dd-e5c10db820fd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_mem_pairs
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sum_pairs

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
theorem _root_.solution {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (P : Finset (T × ℕ))
    (m : Multiset (ASeg T)) (hm : ∀ Δ ∈ m, pairs s Δ ⊆ P) :
    sqLen m = ∑ q ∈ P, wd q.2 * rank s m q.1 q.2 := by
  revert hm
  induction m using Multiset.induction_on with
  | empty => intro _; simp [sqLen, rank]
  | cons Δ m ih =>
    intro hm
    have hΔ := hm Δ (by simp)
    have ih' := ih (fun Γ hΓ => hm Γ (by simp [hΓ]))
    have hsplit : ∀ q ∈ P, wd q.2 * rank s (Δ ::ₘ m) q.1 q.2 =
        wd q.2 * rank s m q.1 q.2 + (if Con s q.1 q.2 (Δ.dec s) then wd q.2 else 0) := by
      intro q _
      unfold rank
      rw [Multiset.countP_cons]
      by_cases hc : Con s q.1 q.2 (Δ.dec s)
      · rw [if_pos hc, if_pos hc]
        ring
      · rw [if_neg hc, if_neg hc]
        ring
    have hfil : ∑ q ∈ P, (if Con s q.1 q.2 (Δ.dec s) then wd q.2 else 0) = Δ.len ^ 2 := by
      rw [← Finset.sum_filter, ← sum_pairs hs hp Δ]
      congr 1
      ext q
      rw [Finset.mem_filter, mem_pairs hs hp]
      exact ⟨fun h => h.2, fun h => ⟨hΔ ((mem_pairs hs hp).2 h), h⟩⟩
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hfil, ← ih']
    simp only [sqLen, Multiset.map_cons, Multiset.sum_cons]
    ring
end GlobalTheory.CompanionTheory.MultiSeg.Rank
