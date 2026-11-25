-- Prove2me | solution 1 for GlobalTheory.BadShare.card_mem_cycleType_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:39.989012+00:00
-- url     : https://prove2.me/submissions/231b2b92-10c6-4372-b533-fa0f91ab516b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardCycleTypeConsMul
import Theorems.Thm_GlobalTheory_BadShare_card_cycleType_cons_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
open Equiv Finset
namespace GlobalTheory.BadShare
theorem _root_.solution (N p : ℕ) (hp : 2 ≤ p) (hN : N < 2 * p) (hpN : p ≤ N) :
    (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p = N.factorial := by
  have hTm : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
      m.sum ≤ N - p ∧ ∀ a ∈ m, 2 ≤ a := by
    intro m hm
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hm
    refine ⟨?_, fun a ha => Perm.two_le_of_mem_cycleType ha⟩
    simpa using τ.sum_cycleType_le
  have hpT : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType, p ∉ m := by
    intro m hm hpm
    have h1 := Multiset.le_sum_of_mem hpm
    have h2 := (hTm m hm).1
    omega
  have hfib : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card =
      ∑ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
        (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin N) => σ.cycleType.erase p)
      (t := (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType)]
    · refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        rw [← h2, Multiset.cons_erase h1]
      · intro h
        rw [h]
        exact ⟨Multiset.mem_cons_self _ _, Multiset.erase_cons_head _ _⟩
    · intro σ hσ
      have hσ' : p ∈ σ.cycleType := by simpa using hσ
      have hsum := Multiset.sum_erase hσ'
      have hle := σ.sum_cycleType_le
      rw [Fintype.card_fin] at hle
      have hc : (σ.cycleType.erase p).sum ≤ Fintype.card (Fin (N - p)) ∧
          ∀ a ∈ σ.cycleType.erase p, 2 ≤ a := by
        refine ⟨by rw [Fintype.card_fin]; omega, fun a ha => ?_⟩
        exact Perm.two_le_of_mem_cycleType (Multiset.mem_of_mem_erase ha)
      obtain ⟨τ, hτ⟩ := (Perm.exists_with_cycleType_iff (Fin (N - p))).2 hc
      exact Finset.mem_image.2 ⟨τ, Finset.mem_univ _, hτ⟩
  have hmain : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p * (N - p).factorial
      = N.factorial * (N - p).factorial := by
    rw [hfib, Finset.sum_mul, Finset.sum_mul,
      Finset.sum_congr rfl fun m hm =>
        card_cycleType_cons_mul N p hp hpN m (hpT m hm) (hTm m hm).1 (hTm m hm).2,
      ← Finset.mul_sum]
    congr 1
    have hc := Finset.card_eq_sum_card_image Perm.cycleType (univ : Finset (Perm (Fin (N - p))))
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hc
    exact hc.symm
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) hmain
end GlobalTheory.BadShare
