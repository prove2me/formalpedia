-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:22:15.171123+00:00
-- url     : https://prove2.me/submissions/1a8baf86-dcfa-409b-ab03-dc460e2a1acf

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_rank_le
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_mem_pairs
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sqLen_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_eq_of_rank

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
theorem _root_.solution {T : Type u} (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (L : List (ASeg T)) (n : Multiset (ASeg T))
    (hL : AOrdered s L) (hn : InSh s n (wt s L)) (hne : n ≠ (L : Multiset (ASeg T))) :
    sqLen n < sqLen (L : Multiset (ASeg T)) := by
  set P : Finset (T × ℕ) := (n + (L : Multiset (ASeg T))).toFinset.biUnion (pairs s) with hPdef
  have hsub : ∀ m : Multiset (ASeg T), (∀ Δ ∈ m, Δ ∈ n + (L : Multiset (ASeg T))) →
      ∀ Δ ∈ m, pairs s Δ ⊆ P := by
    intro m hm Δ hΔ
    exact Finset.subset_biUnion_of_mem (pairs s) (Multiset.mem_toFinset.2 (hm Δ hΔ))
  have e1 := sqLen_eq hs hp P n (hsub n fun Δ h => Multiset.mem_add.2 (Or.inl h))
  have e2 := sqLen_eq hs hp P L (hsub L fun Δ h => Multiset.mem_add.2 (Or.inr h))
  have hle : ∀ q ∈ P, wd q.2 * rank s n q.1 q.2 ≤ wd q.2 * rank s L q.1 q.2 :=
    fun q _ => Nat.mul_le_mul_left _ (rank_le s hs hp hL hn q.1 q.2)
  rw [e1, e2]
  by_contra hnot
  have hsum : ∑ q ∈ P, wd q.2 * rank s n q.1 q.2 = ∑ q ∈ P, wd q.2 * rank s L q.1 q.2 :=
    le_antisymm (Finset.sum_le_sum hle) (not_lt.1 hnot)
  have heq : ∀ q ∈ P, wd q.2 * rank s n q.1 q.2 = wd q.2 * rank s L q.1 q.2 :=
    (Finset.sum_eq_sum_iff_of_le hle).1 hsum
  apply hne
  apply eq_of_rank hs hp _ n L le_rfl
  intro u d
  by_cases hq : (u, d) ∈ P
  · have h := heq (u, d) hq
    have hw : 0 < wd d := by
      unfold wd
      split_ifs <;> norm_num
    exact Nat.eq_of_mul_eq_mul_left hw h
  · have h0 : ∀ m : Multiset (ASeg T), (∀ Δ ∈ m, Δ ∈ n + (L : Multiset (ASeg T))) →
        rank s m u d = 0 := by
      intro m hm
      unfold rank
      rw [Multiset.countP_eq_zero]
      intro Δ hΔ hc
      exact hq (hsub m hm Δ hΔ ((mem_pairs hs hp (q := (u, d))).2 hc))
    rw [h0 n (fun Δ h => Multiset.mem_add.2 (Or.inl h)),
      h0 L (fun Δ h => Multiset.mem_add.2 (Or.inr h))]
end GlobalTheory.CompanionTheory.MultiSeg.Rank
