-- Prove2me | solution 1 for HammingSumset729.Approximation.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:38:05.232395+00:00
-- url     : https://prove2.me/submissions/ed804937-125d-41bc-98b7-fa8f06488d39

import Definitions.Def_HammingSumset729_Approximation_Strings

set_option autoImplicit false
open scoped ENNReal NNReal
open HammingSumset729.Approximation

/-- Column with an index offset `k`. -/
private def F {α : Type*} (ell i : ℕ) (l : List α) (k : ℕ) : List α :=
  ((l.zipIdx k).filter fun ai => ai.2 % ell = i).map Prod.fst

private lemma F_nil {α : Type*} (ell i k : ℕ) : F ell i ([] : List α) k = [] := by
  simp [F]

private lemma F_cons {α : Type*} (ell i : ℕ) (a : α) (l : List α) (k : ℕ) :
    F ell i (a :: l) k = (if k % ell = i then [a] else []) ++ F ell i l (k + 1) := by
  by_cases h : k % ell = i <;> simp [F, List.zipIdx_cons, h]

private lemma F_append {α : Type*} (ell i : ℕ) (l₁ l₂ : List α) (k : ℕ) :
    F ell i (l₁ ++ l₂) k = F ell i l₁ k ++ F ell i l₂ (k + l₁.length) := by
  simp [F, List.zipIdx_append, List.filter_append]

private lemma F_shift {α : Type*} (ell i : ℕ) (l : List α) (k : ℕ) :
    F ell i l (k + ell) = F ell i l k := by
  induction l generalizing k with
  | nil => simp [F_nil]
  | cons a l ih =>
    rw [F_cons, F_cons, Nat.add_mod_right, show k + ell + 1 = (k + 1) + ell by omega, ih]

private lemma F_blk {α : Type*} (ell i : ℕ) (hi : i < ell) (a : List α) (k : ℕ)
    (hk : k + a.length ≤ ell) :
    F ell i a k = if k ≤ i then (a[i - k]?).toList else [] := by
  induction a generalizing k with
  | nil => simp [F_nil]
  | cons x l ih =>
    simp only [List.length_cons] at hk
    rw [F_cons, ih (k + 1) (by omega), Nat.mod_eq_of_lt (by omega : k < ell)]
    rcases lt_trichotomy k i with h | h | h
    · have e : i - k = (i - (k + 1)) + 1 := by omega
      rw [if_neg h.ne, if_pos (by omega), if_pos h.le, e, List.getElem?_cons_succ]
      simp
    · subst h
      simp
    · rw [if_neg h.ne', if_neg (by omega), if_neg (by omega)]
      simp

private lemma column_eq_F {α : Type*} (s : List α) (ell i : ℕ) :
    column s ell i = F ell i s 0 := rfl

private lemma column_split {α : Type*} (b : List α) (ell i : ℕ) (hi : i < ell) :
    column b ell i = (b[i]?).toList ++ column (b.drop ell) ell i := by
  rw [column_eq_F, column_eq_F]
  conv_lhs => rw [← List.take_append_drop ell b]
  rw [F_append, F_blk ell i hi _ 0 (by simp), if_pos (Nat.zero_le _), Nat.sub_zero,
    List.getElem?_take_of_lt hi]
  congr 1
  by_cases h : ell ≤ b.length
  · rw [List.length_take, min_eq_left h]
    simpa using F_shift ell i (b.drop ell) 0
  · have : b.drop ell = [] := List.drop_eq_nil_of_le (by omega)
    rw [this, F_nil, F_nil]

private lemma column_head {α : Type*} (b : List α) (ell i : ℕ) (hi : i < ell) :
    (column b ell i).head? = b[i]? := by
  rw [column_split b ell i hi]
  cases h : b[i]? with
  | some y => simp
  | none =>
    have h1 : b.length ≤ i := by simpa using h
    have : b.drop ell = [] := List.drop_eq_nil_of_le (by omega)
    simp [this, column_eq_F, F_nil]

private lemma runs_cons {α : Type*} [DecidableEq α] (x : α) (l : List α) :
    runs (x :: l) = runs l + if l.head? = some x then 0 else 1 := by
  cases l with
  | nil => simp [runs]
  | cons y l =>
    simp only [runs, List.zip_cons_cons, List.countP_cons, List.head?_cons]
    by_cases h : y = x
    · subst h; simp
    · simp [h, Ne.symm h]; omega

private def T {α : Type*} [DecidableEq α] (p : List α) (ell j : ℕ) : ℕ :=
  if p[j]? ≠ none ∧ p[j + ell]? ≠ p[j]? then 1 else 0

private lemma runs_col_step {α : Type*} [DecidableEq α] (p : List α) (ell i : ℕ)
    (hi : i < ell) :
    runs (column p ell i) ≤ runs (column (p.drop ell) ell i) + T p ell i := by
  rw [column_split p ell i hi]
  cases h : p[i]? with
  | none => simp [T, h]
  | some x =>
    simp only [Option.toList_some, List.singleton_append]
    rw [runs_cons, column_head _ _ _ hi, List.getElem?_drop, Nat.add_comm ell i]
    unfold T
    rw [h]
    by_cases h2 : p[i + ell]? = some x <;> simp [h2]

private lemma T_zero {α : Type*} [DecidableEq α] (p : List α) (ell j : ℕ)
    (hj : p.length ≤ j) : T p ell j = 0 := by
  simp [T, List.getElem?_eq_none hj]

private lemma T_drop {α : Type*} [DecidableEq α] (p : List α) (ell j : ℕ) :
    T (p.drop ell) ell j = T p ell (ell + j) := by
  simp [T, List.getElem?_drop, Nat.add_assoc]

private lemma sum_T_ext {α : Type*} [DecidableEq α] (p : List α) (ell N : ℕ)
    (hN : p.length ≤ N) :
    ∑ j ∈ Finset.range N, T p ell j = ∑ j ∈ Finset.range p.length, T p ell j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range d)
    (fun x _ => T_zero p ell _ (by omega)), add_zero]

private lemma S_step {α : Type*} [DecidableEq α] (p : List α) (ell : ℕ) :
    ∑ j ∈ Finset.range p.length, T p ell j =
      ∑ i ∈ Finset.range ell, T p ell i +
        ∑ j ∈ Finset.range (p.drop ell).length, T (p.drop ell) ell j := by
  rw [← sum_T_ext p ell (ell + p.length) (by omega), Finset.sum_range_add,
    ← sum_T_ext (p.drop ell) ell p.length (by simp)]
  simp [T_drop]

private lemma sum_list_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

private lemma C_le_S {α : Type*} [DecidableEq α] (ell : ℕ) (hell : 0 < ell) :
    ∀ n, ∀ p : List α, p.length = n →
      ∑ i ∈ Finset.range ell, runs (column p ell i) ≤
        ∑ j ∈ Finset.range p.length, T p ell j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    by_cases hp0 : p = []
    · subst hp0
      simp [column_eq_F, F, runs]
    · have hlen : 0 < p.length := List.length_pos_iff.mpr hp0
      have hlt : (p.drop ell).length < n := by simp; omega
      have IH := ih _ hlt _ rfl
      rw [S_step]
      calc ∑ i ∈ Finset.range ell, runs (column p ell i)
          ≤ ∑ i ∈ Finset.range ell, (runs (column (p.drop ell) ell i) + T p ell i) :=
            Finset.sum_le_sum (fun i hi => runs_col_step _ _ _ (Finset.mem_range.mp hi))
        _ = ∑ i ∈ Finset.range ell, runs (column (p.drop ell) ell i) +
              ∑ i ∈ Finset.range ell, T p ell i := Finset.sum_add_distrib
        _ ≤ _ := by omega

private lemma dist_eq {α : Type*} [DecidableEq α] : ∀ (s t : List α), s.length = t.length →
    distance s t = ∑ j ∈ Finset.range s.length, if s[j]? ≠ t[j]? then 1 else 0
  | [], [], _ => by simp [distance]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: s, y :: t, h => by
    rw [List.length_cons, Finset.sum_range_succ']
    have IH := dist_eq s t (by simpa using h)
    simp only [distance] at IH ⊢
    rw [List.zip_cons_cons, List.filter_cons]
    by_cases hxy : x = y
    · simp [hxy] at IH ⊢; omega
    · simp [hxy] at IH ⊢; omega

private lemma S_le {α : Type*} [DecidableEq α] (p : List α) (ell : ℕ) (h : ell ≤ p.length) :
    ∑ j ∈ Finset.range p.length, T p ell j ≤
      ell + distance (p.drop ell) (p.take (p.length - ell)) := by
  rw [dist_eq _ _ (by simp)]
  have e : p.length = (p.length - ell) + ell := by omega
  rw [e, Finset.sum_range_add, ← e, add_comm ell]
  apply add_le_add
  · rw [List.length_drop]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j < p.length - ell := Finset.mem_range.mp hj
    rw [List.getElem?_drop, List.getElem?_take_of_lt hj', Nat.add_comm ell j]
    unfold T
    by_cases h2 : p[j + ell]? = p[j]? <;> simp [h2]
    split_ifs <;> omega
  · calc ∑ x ∈ Finset.range ell, T p ell (p.length - ell + x)
        ≤ ∑ x ∈ Finset.range ell, 1 :=
          Finset.sum_le_sum (fun x _ => by unfold T; split_ifs <;> simp)
      _ = ell := by simp

theorem solution {α : Type*} [DecidableEq α] (p : List α) (k ell : ℕ)
    (hk : k ≤ p.length) (hperiod : IsPeriod p (8 * k) ell) (hell : ell ≤ k) :
    runsByPeriod p ell ≤ 9 * k := by
  obtain ⟨hpos, hle, hdist⟩ := hperiod
  have hD : distance (p.drop ell) (p.take (p.length - ell)) ≤ 8 * k := by
    exact_mod_cast hdist
  have h1 : runsByPeriod p ell =
      ∑ i ∈ Finset.range ell, runs (column p ell i) := by
    rw [runsByPeriod, sum_list_range]
  have h2 := C_le_S (α := α) ell hpos p.length p rfl
  have h3 := S_le p ell hle
  omega
