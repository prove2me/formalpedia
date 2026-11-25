-- Prove2me | solution 1 for GlobalTheory.BadShare.card_cycleType_cons_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:05:00.530403+00:00
-- url     : https://prove2.me/submissions/6c5b78ba-e511-4c28-a212-c1be05c98e29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardCycleTypeConsMul

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
theorem _root_.solution (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N) (m : Multiset ℕ)
    (hpm : p ∉ m) (hs : m.sum ≤ N - p) (h2 : ∀ a ∈ m, 2 ≤ a) :
    (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card * p * (N - p).factorial
      = N.factorial * (univ.filter fun σ : Perm (Fin (N - p)) => σ.cycleType = m).card := by
  have hA := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin N) (p ::ₘ m)
  have hB := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin (N - p)) m
  rw [Fintype.card_fin] at hA hB
  have hcA : (p ::ₘ m).sum ≤ N ∧ ∀ a ∈ p ::ₘ m, 2 ≤ a := by
    refine ⟨by rw [Multiset.sum_cons]; omega, fun a ha => ?_⟩
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · exact hp
    · exact h2 a ha
  rw [if_pos hcA] at hA
  rw [if_pos ⟨hs, h2⟩] at hB
  have hsum : N - (p ::ₘ m).sum = N - p - m.sum := by
    rw [Multiset.sum_cons, Nat.sub_sub]
  have hfac : ∏ n ∈ (p ::ₘ m).toFinset, ((p ::ₘ m).count n).factorial =
      ∏ n ∈ m.toFinset, (m.count n).factorial := by
    rw [Multiset.toFinset_cons, Finset.prod_insert (by simpa using hpm), Multiset.count_cons_self,
      Multiset.count_eq_zero.2 hpm, zero_add, Nat.factorial_one, one_mul]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hne : n ≠ p := fun h => hpm (h ▸ Multiset.mem_toFinset.1 hn)
    rw [Multiset.count_cons_of_ne hne]
  rw [hsum, Multiset.prod_cons, hfac] at hA
  rw [← hB, ← hA]
  ring
end GlobalTheory.BadShare
