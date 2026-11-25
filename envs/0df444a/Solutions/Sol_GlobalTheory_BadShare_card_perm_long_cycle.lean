-- Prove2me | solution 1 for GlobalTheory.BadShare.card_perm_long_cycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:14.197481+00:00
-- url     : https://prove2.me/submissions/417a71a2-a15d-4843-8217-3737c656b24c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardCycleTypeConsMul
import Theorems.Thm_GlobalTheory_BadShare_card_mem_cycleType_mul

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
theorem _root_.solution : ∀ N p : ℕ, N < 2 * p → p ≤ N →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card * p
      = N.factorial := by
  intro N p hN hpN
  rcases Nat.lt_or_ge p 2 with hp | hp
  · obtain rfl : p = 1 := by omega
    obtain rfl : N = 1 := by omega
    have hall : ∀ σ : Equiv.Perm (Fin 1), 1 ∈ σ.partition.parts := by
      intro σ
      have hs : σ.partition.parts.sum = 1 := σ.partition.parts_sum.trans (Fintype.card_fin 1)
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (s := σ.partition.parts)
        (fun h => by rw [h, Multiset.sum_zero] at hs; exact absurd hs (by norm_num))
      have h1 := σ.partition.parts_pos ha
      have h2 := Multiset.le_sum_of_mem ha
      obtain rfl : a = 1 := by omega
      exact ha
    rw [Finset.filter_true_of_mem (fun σ _ => hall σ), Finset.card_univ, Fintype.card_perm]
    simp
  · have hiff : ∀ σ : Equiv.Perm (Fin N), p ∈ σ.partition.parts ↔ p ∈ σ.cycleType := by
      intro σ
      rw [Equiv.Perm.parts_partition, Multiset.mem_add]
      constructor
      · rintro (h | h)
        · exact h
        · have := Multiset.eq_of_mem_replicate h
          omega
      · exact Or.inl
    simp_rw [hiff]
    exact card_mem_cycleType_mul N p hp hN hpN
end GlobalTheory.BadShare
