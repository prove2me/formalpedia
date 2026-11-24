-- Prove2me | solution 1 for IncrOpenAddr.NoTradeoff.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:57:22.983031+00:00
-- url     : https://prove2.me/submissions/123e8706-247b-42a8-8ce4-83a8e8cd8e7a

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout

namespace SolIncrOpenAddrEq3

open IncrOpenAddr.NoTradeoff

/-- The block of events spent on tree `2^a + t` in round `r` (the body of `roundEvents`). -/
def blk (α : ℕ) (len : ℕ → ℕ) (r a t : ℕ) : List (Option (ℕ × ℕ)) :=
  if 2 ^ a + t ≤ α then
    (List.range (min (2 ^ ((r - a) / 2)) (len (2 ^ a + t)))).map (fun k => some (2 ^ a + t, k + 1))
  else List.replicate (2 ^ ((r - a) / 2)) none

/-- All blocks of level `a` (trees `2^a, …, 2^(a+1) - 1`) in round `r`. -/
def lvl (α : ℕ) (len : ℕ → ℕ) (r a : ℕ) : List (Option (ℕ × ℕ)) :=
  (List.range (2 ^ a)).flatMap (blk α len r a)

theorem roundEventsEq (α : ℕ) (len : ℕ → ℕ) (r : ℕ) :
    roundEvents α len r = (List.range (r + 1)).flatMap (lvl α len r) := rfl

theorem len_flatMap_range_le {β : Type} (f : ℕ → List β) (g : ℕ → ℕ) :
    ∀ m, (∀ x < m, (f x).length ≤ g x) →
      ((List.range m).flatMap f).length ≤ ∑ x ∈ Finset.range m, g x
  | 0, _ => by simp
  | m + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append, Finset.sum_range_succ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact Nat.add_le_add (len_flatMap_range_le f g m (fun x hx => h x (by omega))) (h m (by omega))

theorem range_split (a : ℕ) : ∀ m, a < m → ∃ rest, List.range m = List.range a ++ a :: rest
  | 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · obtain ⟨rest, hr⟩ := range_split a m h'
      exact ⟨rest ++ [m], by rw [List.range_succ, hr]; simp⟩
    · subst h'; exact ⟨[], by rw [List.range_succ]⟩

theorem get_shift {β : Type} (A B : List β) (j : ℕ) : (A ++ B)[A.length + j]? = B[j]? := by
  rw [List.getElem?_append_right (by omega)]
  congr 1; omega

theorem get_left {β : Type} (B C : List β) (j : ℕ) (x : β) (h : B[j]? = some x) :
    (B ++ C)[j]? = some x := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h

/-- `W r = Σ_{a ≤ r} 2^a 2^⌊(r-a)/2⌋`, the maximal number of events of round `r`. -/
def W (r : ℕ) : ℕ := ∑ a ∈ Finset.range (r + 1), 2 ^ a * 2 ^ ((r - a) / 2)

theorem W_le : ∀ r, W r ≤ 3 * 2 ^ r
  | 0 => by simp [W]
  | 1 => by simp [W, Finset.sum_range_succ]
  | r + 2 => by
    have ih := W_le r
    unfold W at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have e : ∑ a ∈ Finset.range (r + 1), 2 ^ a * 2 ^ ((r + 2 - a) / 2)
        = 2 * ∑ a ∈ Finset.range (r + 1), 2 ^ a * 2 ^ ((r - a) / 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_range] at ha
      rw [show (r + 2 - a) / 2 = (r - a) / 2 + 1 by omega, pow_succ]; ring
    rw [e, show (r + 2 - (r + 1)) / 2 = 0 by omega, show (r + 2 - (r + 2)) / 2 = 0 by omega]
    have h1 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    have h2 : 2 ^ (r + 2) = 4 * 2 ^ r := by ring
    rw [h1, h2]
    simp only [pow_zero, mul_one]
    omega

theorem blk_len (α : ℕ) (len : ℕ → ℕ) (r a t : ℕ) : (blk α len r a t).length ≤ 2 ^ ((r - a) / 2) := by
  unfold blk
  split_ifs
  · simp
  · simp

theorem lvl_len (α : ℕ) (len : ℕ → ℕ) (r a : ℕ) :
    (lvl α len r a).length ≤ 2 ^ a * 2 ^ ((r - a) / 2) := by
  unfold lvl
  calc _ ≤ ∑ x ∈ Finset.range (2 ^ a), 2 ^ ((r - a) / 2) :=
        len_flatMap_range_le _ _ _ (fun t _ => blk_len α len r a t)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem round_len (α : ℕ) (len : ℕ → ℕ) (r : ℕ) : (roundEvents α len r).length ≤ 3 * 2 ^ r := by
  rw [roundEventsEq]
  calc _ ≤ ∑ a ∈ Finset.range (r + 1), 2 ^ a * 2 ^ ((r - a) / 2) :=
        len_flatMap_range_le _ _ _ (fun a _ => lvl_len α len r a)
    _ ≤ 3 * 2 ^ r := W_le r

theorem geom_lt : ∀ r, ∑ x ∈ Finset.range r, 2 ^ x < 2 ^ r
  | 0 => by simp
  | r + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := geom_lt r
    omega

end SolIncrOpenAddrEq3

open IncrOpenAddr.NoTradeoff SolIncrOpenAddrEq3 in
theorem solution :
    ∀ n : ℕ, 8 ≤ n → ∀ (leaf : ℕ → ℕ) (i k : ℕ), 1 ≤ i → i ≤ numTrees n → 1 ≤ k →
      k ≤ (localList n i (leaf i)).length →
      ∃ R p : ℕ, p < 16 * i * k ^ 2 ∧ (scheduleEvents n leaf R)[p]? = some (some (i, k)) := by
  classical
  intro n _ leaf i k hi hiα hk hklen
  set α := numTrees n with hαdef
  set len : ℕ → ℕ := fun i => (localList n i (leaf i)).length with hlen
  -- the level `a` and offset `t` of tree `i`
  set a := Nat.log 2 i with hadef
  have ha1 : 2 ^ a ≤ i := Nat.pow_log_le_self 2 (by omega)
  have ha2 : i < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) i
  set t := i - 2 ^ a with htdef
  have ht : t < 2 ^ a := by rw [pow_succ] at ha2; omega
  have hit : 2 ^ a + t = i := by omega
  -- the least `c` with `k ≤ 2^c`
  have hex : ∃ c, k ≤ 2 ^ c := ⟨k, Nat.lt_two_pow_self.le⟩
  set c := Nat.find hex with hcdef
  have hc1 : k ≤ 2 ^ c := Nat.find_spec hex
  have hc2 : 2 ^ c < 2 * k := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0]; omega
    · have := Nat.find_min hex (show c - 1 < c by omega)
      rw [not_le] at this
      calc 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
        _ < 2 * k := by omega
  set r := a + 2 * c with hrdef
  set X := (List.range a).flatMap (lvl α len r) with hX
  set Y := (List.range t).flatMap (blk α len r a) with hY
  refine ⟨r + 1, (scheduleEvents n leaf r).length + (X.length + (Y.length + (k - 1))), ?_, ?_⟩
  · -- the position bound
    have hS : (scheduleEvents n leaf r).length ≤ 3 * 2 ^ r := by
      unfold scheduleEvents
      calc _ ≤ ∑ x ∈ Finset.range r, 3 * 2 ^ x :=
            len_flatMap_range_le _ _ _ (fun x _ => round_len _ _ x)
        _ ≤ 3 * 2 ^ r := by rw [← Finset.mul_sum]; have := geom_lt r; omega
    have hXl : X.length ≤ 2 ^ c * (2 * 2 ^ a) := by
      have h1 : X.length ≤ ∑ x ∈ Finset.range a, 2 ^ x * 2 ^ ((r - x) / 2) :=
        len_flatMap_range_le _ _ _ (fun x _ => lvl_len α len r x)
      have h2 : ∑ x ∈ Finset.range a, 2 ^ x * 2 ^ ((r - x) / 2)
          = 2 ^ c * ∑ x ∈ Finset.range a, 2 ^ x * 2 ^ ((a - x) / 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_range] at hx
        rw [show (r - x) / 2 = c + (a - x) / 2 by omega, pow_add]; ring
      have h3 := W_le a
      unfold W at h3
      rw [Finset.sum_range_succ, Nat.sub_self, Nat.zero_div, pow_zero, mul_one] at h3
      rw [h2] at h1
      calc X.length ≤ _ := h1
        _ ≤ 2 ^ c * (2 * 2 ^ a) := Nat.mul_le_mul_left _ (by omega)
    have hYl : Y.length ≤ t * 2 ^ c := by
      calc Y.length ≤ ∑ x ∈ Finset.range t, 2 ^ ((r - a) / 2) :=
            len_flatMap_range_le _ _ _ (fun x _ => blk_len α len r a x)
        _ = t * 2 ^ c := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, show (r - a) / 2 = c by omega]
    have hr : 2 ^ r = 2 ^ a * 2 ^ c * 2 ^ c := by rw [hrdef, pow_add, two_mul, pow_add]; ring
    rw [hr] at hS
    -- abbreviations
    have htP : t * 2 ^ c ≤ 2 ^ a * 2 ^ c := Nat.mul_le_mul_right _ ht.le
    have hmain : 2 ^ a * 2 ^ c * (2 ^ c + 1) ≤ i * (2 * k) * (2 * k) :=
      Nat.mul_le_mul (Nat.mul_le_mul ha1 (by omega)) (by omega)
    have hexp : 2 ^ a * 2 ^ c * (2 ^ c + 1) = 2 ^ a * 2 ^ c * 2 ^ c + 2 ^ a * 2 ^ c := by ring
    have hexp2 : i * (2 * k) * (2 * k) = 4 * (i * k * k) := by ring
    have hexp3 : 2 ^ c * (2 * 2 ^ a) = 2 * (2 ^ a * 2 ^ c) := by ring
    have hk2 : 16 * i * k ^ 2 = 16 * (i * k * k) := by ring
    have hkw : k ≤ i * k * k := by
      calc k = 1 * 1 * k := by ring
        _ ≤ i * k * k := Nat.mul_le_mul (Nat.mul_le_mul hi hk) le_rfl
    rw [hexp3] at hXl
    omega
  · -- the event at that position
    have hsched : scheduleEvents n leaf (r + 1)
        = scheduleEvents n leaf r ++ roundEvents α len r := by
      unfold scheduleEvents
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      try rfl
    obtain ⟨restA, hA⟩ := range_split a (r + 1) (by omega)
    have hround : roundEvents α len r = X ++ (lvl α len r a ++ restA.flatMap (lvl α len r)) := by
      rw [roundEventsEq, hA, List.flatMap_append, List.flatMap_cons]
    obtain ⟨restT, hT⟩ := range_split t (2 ^ a) ht
    have hlvl : lvl α len r a = Y ++ (blk α len r a t ++ restT.flatMap (blk α len r a)) := by
      unfold lvl
      rw [hT, List.flatMap_append, List.flatMap_cons]
    have hblk : (blk α len r a t)[k - 1]? = some (some (i, k)) := by
      have hra : (r - a) / 2 = c := by omega
      have hlt : k - 1 < min (2 ^ ((r - a) / 2)) (len (2 ^ a + t)) := by
        rw [hra, hit]
        exact lt_min (by omega) (by simp only [hlen]; omega)
      unfold blk
      rw [if_pos (by rw [hit]; exact hiα), List.getElem?_map, List.getElem?_range hlt]
      simp [hit, Nat.sub_add_cancel hk]
    rw [hsched, get_shift, hround, get_shift, hlvl, List.append_assoc, get_shift]
    exact get_left _ _ _ _ (get_left _ _ _ _ hblk)
