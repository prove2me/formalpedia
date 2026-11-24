-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.eq_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:45.885182+00:00
-- url     : https://prove2.me/submissions/b81d8fee-6e46-4f14-9727-3c9bfad24e5f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_mem_of_rank

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
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) : ∀ (k : ℕ) (n m : Multiset (ASeg T)),
    Multiset.card n + Multiset.card m ≤ k → (∀ u d, rank s n u d = rank s m u d) → n = m := by
  intro k
  induction k with
  | zero =>
    intro n m hk _
    rw [Multiset.card_eq_zero.1 (by omega : Multiset.card n = 0),
      Multiset.card_eq_zero.1 (by omega : Multiset.card m = 0)]
  | succ k ih =>
    intro n m hk hr
    by_cases h0 : n + m = 0
    · have hc := congrArg Multiset.card h0
      rw [Multiset.card_add, Multiset.card_zero] at hc
      rw [Multiset.card_eq_zero.1 (by omega : Multiset.card n = 0),
        Multiset.card_eq_zero.1 (by omega : Multiset.card m = 0)]
    · obtain ⟨Δ, hΔ, hmax⟩ := Multiset.exists_max_image (fun Γ : ASeg T => Γ.len) h0
      have key : ∀ (a b : Multiset (ASeg T)), (∀ u d, rank s a u d = rank s b u d) → Δ ∈ a →
          (∀ Γ ∈ a + b, Γ.len ≤ Δ.len) → Δ ∈ a ∧ Δ ∈ b := by
        intro a b hab ha hm
        exact ⟨ha, mem_of_rank hs hp ha (fun Γ hΓ => hm Γ (Multiset.mem_add.2 (Or.inr hΓ)))
          (hab _ _)⟩
      have hboth : Δ ∈ n ∧ Δ ∈ m := by
        rcases Multiset.mem_add.1 hΔ with h | h
        · exact key n m hr h hmax
        · have := key m n (fun u d => (hr u d).symm) h
            (fun Γ hΓ => hmax Γ (by rw [add_comm]; exact hΓ))
          exact ⟨this.2, this.1⟩
      obtain ⟨n', rfl⟩ := Multiset.exists_cons_of_mem hboth.1
      obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hboth.2
      have hr' : ∀ u d, rank s n' u d = rank s m' u d := by
        intro u d
        have := hr u d
        unfold rank at this ⊢
        rw [Multiset.countP_cons, Multiset.countP_cons] at this
        exact Nat.add_right_cancel this
      have hk' : Multiset.card n' + Multiset.card m' ≤ k := by
        simp only [Multiset.card_cons] at hk
        omega
      rw [ih n' m' hk' hr']
end GlobalTheory.CompanionTheory.MultiSeg.Rank
