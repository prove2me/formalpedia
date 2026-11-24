-- Prove2me | solution 1 for GlobalTheory.ShufflePositions.count_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:32.939427+00:00
-- url     : https://prove2.me/submissions/8f5e3f56-2e3d-4afc-9cd4-f2cff582793b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CountBindWordShuffleByPositions
import Theorems.Thm_GlobalTheory_ShufflePositions_count_cons_map
import Theorems.Thm_GlobalTheory_ShufflePositions_pos_cons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory
namespace GlobalTheory
namespace ShufflePositions
variable {A : Type} [DecidableEq A]
private theorem sum_filter_sub_sum_filter_and_not_eq_sum {M : Type} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → Bool) → M) :
    ∑ ε, f ε = ∑ ε : Fin n → Bool, (f (Fin.cons true ε) + f (Fin.cons false ε)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  rfl
private theorem count_cons_singleton_cons (c a : A) (x u : List A) :
    ({a :: u} : Multiset (List A)).count (c :: x) =
      if c = a then ({u} : Multiset (List A)).count x else 0 := by
  rw [← Multiset.map_singleton (List.cons a) u]
  exact count_cons_map c a x {u}
private theorem count_cons_singleton_nil (c : A) (x : List A) :
    ({[]} : Multiset (List A)).count (c :: x) = 0 := by
  simp
end ShufflePositions
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open GlobalTheory.ShufflePositions
variable {A : Type} [DecidableEq A]
namespace GlobalTheory.ShufflePositions
theorem _root_.solution (n : ℕ) : ∀ (w : Fin n → A) (u v : List A),
    (Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool,
        ({u} : Multiset (List A)).count (((List.finRange n).filter fun j => !ε j).map w) *
        ({v} : Multiset (List A)).count (((List.finRange n).filter ε).map w) := by
  induction n with
  | zero =>
    intro w u v
    simp only [List.ofFn_zero, List.finRange_zero, List.filter_nil, List.map_nil,
      Finset.univ_unique, Finset.sum_singleton]
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simp
    · simp
    · simp [Shuffle.shuffle_nil_right]
    · rw [Shuffle.shuffle_cons_cons]
      simp [Multiset.mem_map]
  | succ n ih =>
    intro w u v
    rw [sum_filter_sub_sum_filter_and_not_eq_sum, List.ofFn_succ]
    simp only [pos_cons, Fin.cons_zero, Fin.cons_succ, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_true, if_false, List.nil_append, List.singleton_append]
    set w' : Fin n → A := fun j => w j.succ with hw'
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simp
    · have h := ih w' [] v
      rw [Shuffle.shuffle_nil_left] at h
      rw [Shuffle.shuffle_nil_left, count_cons_singleton_cons]
      simp only [count_cons_singleton_cons, count_cons_singleton_nil, zero_mul, add_zero]
      by_cases hc : w 0 = b
      · simp only [if_pos hc, h]
      · simp [if_neg hc]
    · have h := ih w' u []
      rw [Shuffle.shuffle_nil_right] at h
      rw [Shuffle.shuffle_nil_right, count_cons_singleton_cons]
      simp only [count_cons_singleton_cons, count_cons_singleton_nil, mul_zero, zero_add]
      by_cases hc : w 0 = a
      · simp only [if_pos hc, h]
      · simp [if_neg hc]
    · have h1 := ih w' u (b :: v)
      have h2 := ih w' (a :: u) v
      rw [Shuffle.shuffle_cons_cons, Multiset.count_add, count_cons_map, count_cons_map]
      simp only [count_cons_singleton_cons, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      · by_cases hc : w 0 = b
        · simp only [if_pos hc, h2]
        · simp [if_neg hc]
      · by_cases hc : w 0 = a
        · simp only [if_pos hc, h1]
        · simp [if_neg hc]
end GlobalTheory.ShufflePositions
