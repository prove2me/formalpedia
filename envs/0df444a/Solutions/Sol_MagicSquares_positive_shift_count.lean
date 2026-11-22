-- Prove2me | solution 1 for MagicSquares.positive_shift_count
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T22:55:44.478019+00:00
-- url     : https://prove2.me/submissions/e45021a4-a4d8-4c02-8cb0-01bc94b1f6a5

import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators
namespace MagicShift
open MagicSquares

lemma sum_pred {n t : ℕ} (a : Fin n → ℕ) (hp : ∀ j, 1 ≤ a j)
    (ha : ∑ j, a j = t) : ∑ j, (a j - 1) = t - n := by
  have he : ∑ j, (a j - 1 + 1) = t := by
    rw [← ha]
    apply Finset.sum_congr rfl
    intro j hj
    exact Nat.sub_add_cancel (hp j)
  have he' : (∑ j, (a j - 1)) + n = t := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] using he
  omega

lemma pred_bound {n t : ℕ} (M : Square n (Fin (t+1)))
    (hm : IsSemiMagic (fun i j => (M i j : ℕ)) t)
    (hp : ∀ i j, 1 ≤ (M i j : ℕ)) (i j : Fin n) :
    (M i j : ℕ) - 1 < t - n + 1 := by
  have hs := sum_pred (fun j => (M i j : ℕ)) (hp i) (hm.1 i)
  have hl := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
    Nat.zero_le ((M i k : ℕ) - 1)) (Finset.mem_univ j)
  rw [hs] at hl
  omega

def down {n t : ℕ} (M : Square n (Fin (t+1)))
    (hm : IsSemiMagic (fun i j => (M i j : ℕ)) t)
    (hp : ∀ i j, 1 ≤ (M i j : ℕ)) : Square n (Fin (t-n+1)) :=
  fun i j => ⟨(M i j : ℕ)-1, pred_bound M hm hp i j⟩

lemma down_semimagic {n t : ℕ} (M : Square n (Fin (t+1)))
    (hm : IsSemiMagic (fun i j => (M i j : ℕ)) t)
    (hp : ∀ i j, 1 ≤ (M i j : ℕ)) :
    IsSemiMagic (fun i j => (down M hm hp i j : ℕ)) (t-n) := by
  constructor
  · intro i
    exact sum_pred (fun j => (M i j : ℕ)) (hp i) (hm.1 i)
  · intro j
    exact sum_pred (fun i => (M i j : ℕ)) (fun i => hp i j) (hm.2 j)

def up {n t : ℕ} (hn : 1 ≤ n) (hnt : n ≤ t)
    (M : Square n (Fin (t-n+1))) : Square n (Fin (t+1)) :=
  fun i j => ⟨(M i j : ℕ)+1, by have h := (M i j).isLt; omega⟩

lemma up_semimagic {n t : ℕ} (hn : 1 ≤ n) (hnt : n ≤ t)
    (M : Square n (Fin (t-n+1)))
    (hm : IsSemiMagic (fun i j => (M i j : ℕ)) (t-n)) :
    IsSemiMagic (fun i j => (up hn hnt M i j : ℕ)) t := by
  constructor
  · intro i
    change (∑ j, ((M i j : ℕ)+1)) = t
    rw [Finset.sum_add_distrib]
    change rowSum (fun i j => (M i j : ℕ)) i + (∑ _ : Fin n, 1) = t
    rw [hm.1 i]
    simpa using Nat.sub_add_cancel hnt
  · intro j
    change (∑ i, ((M i j : ℕ)+1)) = t
    rw [Finset.sum_add_distrib]
    change colSum (fun i j => (M i j : ℕ)) j + (∑ _ : Fin n, 1) = t
    rw [hm.2 j]
    simpa using Nat.sub_add_cancel hnt

end MagicShift

namespace MagicSquares

theorem positive_shift_count (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t) :
    positiveInteriorCount n t = semiMagicCount n (t-n) := by
  classical
  unfold positiveInteriorCount semiMagicCount semiMagicSquares
  let A : Finset (Square n (Fin (t+1))) := Finset.univ.filter (fun M =>
    IsSemiMagic (fun i j => (M i j : ℕ)) t ∧ ∀ i j, 1 ≤ (M i j : ℕ))
  let B : Finset (Square n (Fin (t-n+1))) := Finset.univ.filter (fun M =>
    IsSemiMagic (fun i j => (M i j : ℕ)) (t-n))
  change A.card = B.card
  have ha (M) (hM : M ∈ A) :
      IsSemiMagic (fun i j => (M i j : ℕ)) t ∧ ∀ i j, 1 ≤ (M i j : ℕ) :=
    (Finset.mem_filter.mp hM).2
  have hb (M) (hM : M ∈ B) : IsSemiMagic (fun i j => (M i j : ℕ)) (t-n) :=
    (Finset.mem_filter.mp hM).2
  let d : ∀ M ∈ A, Square n (Fin (t-n+1)) :=
    fun M hM => MagicShift.down M (ha M hM).1 (ha M hM).2
  let u : ∀ M ∈ B, Square n (Fin (t+1)) := fun M _ => MagicShift.up hn hnt M
  have hd : ∀ M hM, d M hM ∈ B := by
    intro M hM
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      MagicShift.down_semimagic M (ha M hM).1 (ha M hM).2⟩
  have hu : ∀ M hM, u M hM ∈ A := by
    intro M hM
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      MagicShift.up_semimagic hn hnt M (hb M hM), fun i j => Nat.le_add_left 1 _⟩
  refine Finset.card_bij' d u hd hu ?_ ?_
  · intro M hM
    funext i j
    apply Fin.ext
    change (M i j : ℕ) - 1 + 1 = (M i j : ℕ)
    exact Nat.sub_add_cancel ((ha M hM).2 i j)
  · intro M hM
    funext i j
    apply Fin.ext
    change (M i j : ℕ) + 1 - 1 = (M i j : ℕ)
    omega

end MagicSquares

theorem solution (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t) :
    MagicSquares.positiveInteriorCount n t = MagicSquares.semiMagicCount n (t-n) :=
  MagicSquares.positive_shift_count n t hn hnt

