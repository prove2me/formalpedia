-- Prove2me | solution 2 for MagicSquares.positive_shift_count
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-20T22:56:48.282858+00:00
-- url     : https://prove2.me/submissions/8e45db22-62dd-4cab-8786-a2f8c95701d4

import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0

open MagicSquares
open scoped BigOperators

namespace MagicSquares

/-- Shift down: subtract one from every entry; the modulus keeps the map total. -/
private def down (n t : ℕ) (M : Square n (Fin (t + 1))) : Square n (Fin (t - n + 1)) :=
  fun i j => ⟨((M i j : ℕ) - 1) % (t - n + 1), Nat.mod_lt _ (by omega)⟩

/-- Shift up: add one to every entry. -/
private def up (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t) (M' : Square n (Fin (t - n + 1))) :
    Square n (Fin (t + 1)) :=
  fun i j => ⟨(M' i j : ℕ) + 1, by
    have hlt : ((M' i j : Fin (t - n + 1)) : ℕ) < t - n + 1 := (M' i j).2
    omega⟩

private lemma down_val (n t : ℕ) (M : Square n (Fin (t + 1))) (i j : Fin n) :
    ((down n t M i j : Fin (t - n + 1)) : ℕ) =
      (((M i j : Fin (t + 1)) : ℕ) - 1) % (t - n + 1) := rfl

private lemma up_val (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t)
    (M' : Square n (Fin (t - n + 1))) (i j : Fin n) :
    ((up n t hn hnt M' i j : Fin (t + 1)) : ℕ) =
      ((M' i j : Fin (t - n + 1)) : ℕ) + 1 := rfl

private lemma h1n (n : ℕ) : (∑ _j : Fin n, (1 : ℕ)) = n := by simp

/-- The interior family as a standalone set. -/
private noncomputable def lhsSet (n t : ℕ) : Finset (Square n (Fin (t + 1))) :=
  by classical exact Finset.univ.filter (fun M : Square n (Fin (t + 1)) =>
    IsSemiMagic (fun i j => (M i j : ℕ)) t ∧ ∀ i j, 1 ≤ (M i j : ℕ))

/-- The ordinary family as a standalone set. -/
private noncomputable def rhsSet (n t : ℕ) : Finset (Square n (Fin (t - n + 1))) :=
  by classical exact Finset.univ.filter (fun M' : Square n (Fin (t - n + 1)) =>
    IsSemiMagic (fun i j => (M' i j : ℕ)) (t - n))

private lemma mem_lhs_iff {n t : ℕ} {M : Square n (Fin (t + 1))} :
    M ∈ lhsSet n t ↔ M ∈ Finset.univ ∧
      (IsSemiMagic (fun i j => (M i j : ℕ)) t ∧ ∀ i j, 1 ≤ (M i j : ℕ)) := by
  unfold lhsSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private lemma mem_rhs_iff {n t : ℕ} {M' : Square n (Fin (t - n + 1))} :
    M' ∈ rhsSet n t ↔ M' ∈ Finset.univ ∧
      IsSemiMagic (fun i j => (M' i j : ℕ)) (t - n) := by
  unfold rhsSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A row (or column) of values summing to `s`, each at least one, has every
truncated predecessor bounded by the modulus. -/
private lemma cell_le {n : ℕ} {f : Fin n → ℕ} {s : ℕ}
    (hsum : ∑ k, f k = s) (hpos : ∀ k, 1 ≤ f k) (j : Fin n) :
    f j - 1 < s - n + 1 := by
  have hcard : (Finset.univ.erase j).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin]
  have h2 : (∑ _k ∈ Finset.univ.erase j, (1 : ℕ)) ≤
      ∑ k ∈ Finset.univ.erase j, f k :=
    Finset.sum_le_sum (fun k _ => hpos k)
  have e : (∑ _k ∈ Finset.univ.erase j, (1 : ℕ)) = n - 1 := by
    rw [Finset.sum_const, hcard]
    simp
  have hsplit : f j + ∑ k ∈ Finset.univ.erase j, f k = ∑ k, f k :=
    Finset.add_sum_erase _ _ (Finset.mem_univ j)
  omega

/-- Row sums, column sums and positivity read off from interior membership. -/
private lemma lhs_facts {n t : ℕ} {M : Square n (Fin (t + 1))} (hM : M ∈ lhsSet n t) :
    (∀ i, (∑ j, ((M i j : Fin (t + 1)) : ℕ)) = t) ∧
    (∀ j, (∑ i, ((M i j : Fin (t + 1)) : ℕ)) = t) ∧
    (∀ i j, 1 ≤ ((M i j : Fin (t + 1)) : ℕ)) := by
  obtain ⟨_, hsemi, hpos⟩ := mem_lhs_iff.mp hM
  refine ⟨?_, ?_, hpos⟩
  · intro i
    simpa [rowSum] using hsemi.1 i
  · intro j
    simpa [colSum] using hsemi.2 j

/-- Row sums and column sums read off from ordinary membership. -/
private lemma rhs_facts {n t : ℕ} {M' : Square n (Fin (t - n + 1))}
    (hM' : M' ∈ rhsSet n t) :
    (∀ i, (∑ j, ((M' i j : Fin (t - n + 1)) : ℕ)) = t - n) ∧
    (∀ j, (∑ i, ((M' i j : Fin (t - n + 1)) : ℕ)) = t - n) := by
  obtain ⟨_, hsemi⟩ := mem_rhs_iff.mp hM'
  refine ⟨?_, ?_⟩
  · intro i
    simpa [rowSum] using hsemi.1 i
  · intro j
    simpa [colSum] using hsemi.2 j

/-- The down-map lands in the ordinary family. -/
private lemma down_mem {n t : ℕ} {M : Square n (Fin (t + 1))} (hM : M ∈ lhsSet n t) :
    down n t M ∈ rhsSet n t := by
  obtain ⟨hrow, hcol, hpos⟩ := lhs_facts hM
  have h1n' : (∑ _j : Fin n, (1 : ℕ)) = n := h1n n
  have Brow : ∀ i j, ((M i j : Fin (t + 1)) : ℕ) - 1 < t - n + 1 :=
    fun i j => cell_le (hrow i) (hpos i) j
  rw [mem_rhs_iff]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i
    have hfsum : (∑ j, ((down n t M i j : Fin (t - n + 1)) : ℕ)) = t - n := by
      have h1 : (∑ j, ((down n t M i j : Fin (t - n + 1)) : ℕ)) =
          ∑ j, (((M i j : Fin (t + 1)) : ℕ) - 1) :=
        Finset.sum_congr rfl (fun j _ => by
          rw [down_val, Nat.mod_eq_of_lt (Brow i j)])
      have hdecomp : (∑ j, ((M i j : Fin (t + 1)) : ℕ)) =
          (∑ j, (((M i j : Fin (t + 1)) : ℕ) - 1)) + n := by
        have hc : (∑ j, ((M i j : Fin (t + 1)) : ℕ)) =
            ∑ j, ((((M i j : Fin (t + 1)) : ℕ) - 1) + 1) :=
          Finset.sum_congr rfl (fun j _ => (Nat.sub_add_cancel (hpos i j)).symm)
        rw [hc, Finset.sum_add_distrib, h1n']
      have hrowi := hrow i
      omega
    simpa [rowSum] using hfsum
  · intro j
    have hfsum : (∑ i, ((down n t M i j : Fin (t - n + 1)) : ℕ)) = t - n := by
      have h1 : (∑ i, ((down n t M i j : Fin (t - n + 1)) : ℕ)) =
          ∑ i, (((M i j : Fin (t + 1)) : ℕ) - 1) :=
        Finset.sum_congr rfl (fun i _ => by
          rw [down_val, Nat.mod_eq_of_lt (Brow i j)])
      have hdecomp : (∑ i, ((M i j : Fin (t + 1)) : ℕ)) =
          (∑ i, (((M i j : Fin (t + 1)) : ℕ) - 1)) + n := by
        have hc : (∑ i, ((M i j : Fin (t + 1)) : ℕ)) =
            ∑ i, ((((M i j : Fin (t + 1)) : ℕ) - 1) + 1) :=
          Finset.sum_congr rfl (fun i _ => (Nat.sub_add_cancel (hpos i j)).symm)
        rw [hc, Finset.sum_add_distrib, h1n']
      have hcolj := hcol j
      omega
    simpa [colSum] using hfsum

/-- The up-map lands in the interior family. -/
private lemma up_mem (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t)
    {M' : Square n (Fin (t - n + 1))}
    (hM' : M' ∈ rhsSet n t) :
    up n t hn hnt M' ∈ lhsSet n t := by
  obtain ⟨hrow', hcol'⟩ := rhs_facts hM'
  have h1n' : (∑ _j : Fin n, (1 : ℕ)) = n := h1n n
  rw [mem_lhs_iff]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · constructor
    · intro i
      have hfsum : (∑ j, ((up n t hn hnt M' i j : Fin (t + 1)) : ℕ)) = t := by
        have h1 : (∑ j, ((up n t hn hnt M' i j : Fin (t + 1)) : ℕ)) =
            ∑ j, (((M' i j : Fin (t - n + 1)) : ℕ) + 1) :=
          Finset.sum_congr rfl (fun j _ => up_val n t hn hnt M' i j)
        rw [h1, Finset.sum_add_distrib, h1n']
        have hrowi := hrow' i
        omega
      simpa [rowSum] using hfsum
    · intro j
      have hfsum : (∑ i, ((up n t hn hnt M' i j : Fin (t + 1)) : ℕ)) = t := by
        have h1 : (∑ i, ((up n t hn hnt M' i j : Fin (t + 1)) : ℕ)) =
            ∑ i, (((M' i j : Fin (t - n + 1)) : ℕ) + 1) :=
          Finset.sum_congr rfl (fun i _ => up_val n t hn hnt M' i j)
        rw [h1, Finset.sum_add_distrib, h1n']
        have hcolj := hcol' j
        omega
      simpa [colSum] using hfsum
  · intro i j
    rw [up_val]
    omega

/-- Round trip on the interior side. -/
private lemma leftInv (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t)
    (M : Square n (Fin (t + 1))) (hM : M ∈ lhsSet n t) :
    up n t hn hnt (down n t M) = M := by
  obtain ⟨hrow, hcol, hpos⟩ := lhs_facts hM
  have Brow : ∀ i j, ((M i j : Fin (t + 1)) : ℕ) - 1 < t - n + 1 :=
    fun i j => cell_le (hrow i) (hpos i) j
  funext i j
  have hvaleq : ((up n t hn hnt (down n t M) i j : Fin (t + 1)) : ℕ) =
      ((M i j : Fin (t + 1)) : ℕ) := by
    rw [up_val, down_val, Nat.mod_eq_of_lt (Brow i j),
      Nat.sub_add_cancel (hpos i j)]
  exact Fin.ext hvaleq

/-- Round trip on the ordinary side. -/
private lemma rightInv (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t)
    (M' : Square n (Fin (t - n + 1))) (_hM' : M' ∈ rhsSet n t) :
    down n t (up n t hn hnt M') = M' := by
  funext i j
  have hlt : ((M' i j : Fin (t - n + 1)) : ℕ) < t - n + 1 := (M' i j).2
  have hvaleq : ((down n t (up n t hn hnt M') i j : Fin (t - n + 1)) : ℕ) =
      ((M' i j : Fin (t - n + 1)) : ℕ) := by
    rw [down_val, up_val, Nat.add_sub_cancel, Nat.mod_eq_of_lt hlt]
  exact Fin.ext hvaleq

end MagicSquares

open MagicSquares

theorem solution (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t) :
    positiveInteriorCount n t = semiMagicCount n (t - n) := by
  show (lhsSet n t).card = (rhsSet n t).card
  refine Finset.card_bij (fun M _ => down n t M) ?_ ?_ ?_
  · intro M hM
    exact down_mem hM
  · intro a ha b hb hab
    have hab' : down n t a = down n t b := hab
    have e1 := leftInv n t hn hnt a ha
    have e2 := leftInv n t hn hnt b hb
    have h := congrArg (up n t hn hnt) hab'
    rw [e1, e2] at h
    exact h
  · intro M' hM'
    exact ⟨up n t hn hnt M', up_mem n t hn hnt hM', rightInv n t hn hnt M' hM'⟩
