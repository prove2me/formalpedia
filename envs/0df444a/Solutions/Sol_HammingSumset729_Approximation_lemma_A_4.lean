-- Prove2me | solution 1 for HammingSumset729.Approximation.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:08:56.349121+00:00
-- url     : https://prove2.me/submissions/64dc7209-8af3-45c3-a6b2-1a237483356c

import Definitions.Def_HammingSumset729_Approximation_Strings
import Theorems.Thm_HammingSumset729_Approximation_lemma_A_3

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
    runs (column p ell i) = runs (column (p.drop ell) ell i) + T p ell i := by
  rw [column_split p ell i hi]
  cases h : p[i]? with
  | none =>
    have h1 : p.length ≤ i := by simpa using h
    have : p.drop ell = [] := List.drop_eq_nil_of_le (by omega)
    simp [T, h, this, column_eq_F, F_nil]
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

private lemma C_eq_S {α : Type*} [DecidableEq α] (ell : ℕ) (hell : 0 < ell) :
    ∀ n, ∀ p : List α, p.length = n →
      ∑ i ∈ Finset.range ell, runs (column p ell i) =
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
          = ∑ i ∈ Finset.range ell, (runs (column (p.drop ell) ell i) + T p ell i) :=
            Finset.sum_congr rfl (fun i hi => runs_col_step _ _ _ (Finset.mem_range.mp hi))
        _ = ∑ i ∈ Finset.range ell, runs (column (p.drop ell) ell i) +
              ∑ i ∈ Finset.range ell, T p ell i := Finset.sum_add_distrib
        _ = _ := by omega

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

/-- Number of period-`ell` changes inside the string. -/
private def Cnt {α : Type*} [DecidableEq α] (ell : ℕ) (s : List α) : ℕ :=
  ∑ j ∈ Finset.range (s.length - ell), if s[j + ell]? ≠ s[j]? then 1 else 0

private lemma runsByPeriod_eq {α : Type*} [DecidableEq α] (s : List α) (ell : ℕ)
    (hell : 0 < ell) :
    runsByPeriod s ell = Cnt ell s + (s.length - (s.length - ell)) := by
  rw [runsByPeriod, sum_list_range, C_eq_S ell hell s.length s rfl, Cnt]
  have e : s.length = (s.length - ell) + (s.length - (s.length - ell)) := by omega
  conv_lhs => rw [e, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < s.length - ell := Finset.mem_range.mp hj
    have h1 : s[j]? ≠ none := by simp; omega
    unfold T
    by_cases h2 : s[j + ell]? = s[j]? <;> simp [h2, h1]
  · rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro x hx
      have hx' := Finset.mem_range.mp hx
      unfold T
      have h1 : s[s.length - ell + x]? ≠ none := by simp; omega
      have h2 : s[s.length - ell + x + ell]? = none := by simp; omega
      rw [if_pos ⟨h1, by rw [h2]; exact Ne.symm h1⟩]

private lemma Cnt_drop {α : Type*} [DecidableEq α] (ell a : ℕ) (s : List α) :
    Cnt ell (s.drop a) ≤ Cnt ell s := by
  unfold Cnt
  rw [List.length_drop]
  by_cases h : s.length - a - ell = 0
  · rw [h]; simp
  · have e : s.length - ell = a + (s.length - a - ell) := by omega
    rw [e, Finset.sum_range_add]
    refine le_add_left (le_of_eq (Finset.sum_congr rfl ?_))
    intro j _
    rw [List.getElem?_drop, List.getElem?_drop, Nat.add_assoc]

private lemma Cnt_take {α : Type*} [DecidableEq α] (ell b : ℕ) (s : List α) :
    Cnt ell (s.take b) ≤ Cnt ell s := by
  unfold Cnt
  rw [List.length_take]
  calc ∑ j ∈ Finset.range (min b s.length - ell),
        (if (s.take b)[j + ell]? ≠ (s.take b)[j]? then 1 else 0)
      = ∑ j ∈ Finset.range (min b s.length - ell), (if s[j + ell]? ≠ s[j]? then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))

private lemma Cnt_perturb {α : Type*} [DecidableEq α] (ell : ℕ) (s u : List α)
    (h : s.length = u.length) :
    Cnt ell s ≤ Cnt ell u + 2 * distance s u := by
  rw [dist_eq s u h]
  unfold Cnt
  rw [← h]
  set L := s.length
  set M : ℕ → ℕ := fun j => if s[j]? ≠ u[j]? then 1 else 0
  have step : ∀ j, (if s[j + ell]? ≠ s[j]? then 1 else 0) ≤
      (if u[j + ell]? ≠ u[j]? then 1 else 0) + M (j + ell) + M j := by
    intro j
    simp only [M]
    by_cases h1 : s[j + ell]? = s[j]? <;> by_cases h2 : u[j + ell]? = u[j]? <;>
      by_cases h3 : s[j + ell]? = u[j + ell]? <;> by_cases h4 : s[j]? = u[j]? <;>
      simp_all
  have hA : ∑ j ∈ Finset.range (L - ell), M (j + ell) ≤ ∑ j ∈ Finset.range L, M j := by
    have e : ∑ j ∈ Finset.range (L - ell), M (j + ell) =
        ∑ j ∈ Finset.range (L - ell), M (ell + j) := by
      apply Finset.sum_congr rfl; intro j _; rw [Nat.add_comm]
    rw [e]
    by_cases hl : ell ≤ L
    · have e2 : L = ell + (L - ell) := by omega
      conv_rhs => rw [e2, Finset.sum_range_add]
      exact le_add_left le_rfl
    · rw [show L - ell = 0 by omega]; simp
  have hB : ∑ j ∈ Finset.range (L - ell), M j ≤ ∑ j ∈ Finset.range L, M j :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  calc _ ≤ ∑ j ∈ Finset.range (L - ell),
        ((if u[j + ell]? ≠ u[j]? then 1 else 0) + M (j + ell) + M j) :=
        Finset.sum_le_sum (fun j _ => step j)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by
      have hf : (Finset.range L).sum M = ∑ j ∈ Finset.range L, M j := rfl
      omega

private lemma foldl_max_ge (l : List ℕ) : ∀ acc, acc ≤ l.foldl max acc ∧
    ∀ a ∈ l, a ≤ l.foldl max acc := by
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    obtain ⟨h1, h2⟩ := ih (max acc x)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    rintro a (rfl | ha)
    · exact le_trans (le_max_right _ _) h1
    · exact h2 a ha

private lemma foldl_max_le (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a ≤ b) :
    ∀ acc, acc ≤ b → l.foldl max acc ≤ b := by
  induction l with
  | nil => intro acc h; simpa using h
  | cons x l ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih (fun a ha => hb a (List.mem_cons_of_mem _ ha)) _
      (max_le h (hb x (List.mem_cons_self)))

private lemma suffix_ge {α : Type*} [DecidableEq α] (s : List α) (ell budget len : ℕ)
    (hlen : len ≤ s.length) (h : runsByPeriod (s.drop (s.length - len)) ell ≤ budget) :
    len ≤ longestSuffixLength s ell budget ∧ longestSuffixLength s ell budget ≤ s.length := by
  unfold longestSuffixLength
  constructor
  · apply (foldl_max_ge _ 0).2
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, h⟩
  · apply foldl_max_le _ _ _ 0 (Nat.zero_le _)
    intro a ha
    simp only [List.mem_filter, List.mem_range] at ha
    omega

private lemma prefix_ge {α : Type*} [DecidableEq α] (s : List α) (ell budget len : ℕ)
    (hlen : len ≤ s.length) (h : runsByPeriod (s.take len) ell ≤ budget) :
    len ≤ longestPrefixLength s ell budget := by
  unfold longestPrefixLength
  apply (foldl_max_ge _ 0).2
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨by omega, h⟩

theorem solution {α : Type*} [DecidableEq α] (t p : List α) (k ell : ℕ)
    (hlen : t.length = 2 * p.length) (hk : k ≤ p.length)
    (hperiod : IsPeriod p (8 * k) ell) (hell : ell ≤ k)
    (i : ℕ) (hi : i ≤ p.length) (hclose : shiftDistance t p i ≤ k) :
    p.length - (trimmedLeft t p.length ell k).length ≤ i ∧
      i + p.length ≤ p.length + (trimmedRight t p.length ell k).length := by
  have hA3 := HammingSumset729.Approximation.lemma_A_3 p k ell hk hperiod hell
  have hpos : 0 < ell := hperiod.1
  set m := p.length with hm
  set W := substring t i m with hW
  have hWlen : W.length = m := by simp [hW, substring]; omega
  have hdist : distance W p ≤ k := hclose
  -- runs of the window
  have hWruns : ∀ Q : List α, Cnt ell Q ≤ Cnt ell W → Q.length ≤ W.length →
      runsByPeriod Q ell ≤ 11 * k := by
    intro Q hQ hQl
    have e1 := runsByPeriod_eq Q ell hpos
    have e2 := runsByPeriod_eq p ell hpos
    have hp := Cnt_perturb ell W p (by omega)
    have hmono : Q.length - (Q.length - ell) ≤ W.length - (W.length - ell) := by omega
    rw [hWlen] at hmono
    omega
  constructor
  · -- left part
    have key : runsByPeriod ((t.take m).drop i) ell ≤ 11 * k := by
      have e : (t.take m).drop i = W.take (m - i) := by
        simp only [hW, substring, List.drop_take, List.take_take]
        congr 1; omega
      rw [e]
      exact hWruns _ (Cnt_take _ _ _) (by simp)
    have hs : (t.take m).length = m := by simp; omega
    have hh := suffix_ge (t.take m) ell (11 * k) (m - i) (by omega)
      (by rw [hs, show m - (m - i) = i by omega]; exact key)
    unfold trimmedLeft
    simp only
    rw [List.length_drop]
    omega
  · have key : runsByPeriod (((t.drop m).take m).take i) ell ≤ 11 * k := by
      have e : ((t.drop m).take m).take i = W.drop (m - i) := by
        simp only [hW, substring, List.drop_take, List.take_take, List.drop_drop]
        rw [show i + (m - i) = m by omega, show m - (m - i) = i by omega, min_eq_left hi]
      rw [e]
      exact hWruns _ (Cnt_drop _ _ _) (by simp)
    have hs : ((t.drop m).take m).length = m := by simp; omega
    have hh := prefix_ge ((t.drop m).take m) ell (11 * k) i (by omega) key
    unfold trimmedRight
    simp only
    rw [List.length_take]
    have : longestPrefixLength ((t.drop m).take m) ell (11 * k) ≤ m := by
      unfold longestPrefixLength
      apply foldl_max_le _ _ _ 0 (Nat.zero_le _)
      intro a ha
      simp only [List.mem_filter, List.mem_range] at ha
      omega
    rw [hs]
    omega
