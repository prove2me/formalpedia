-- Prove2me | solution 1 for IgnallSchrage.MeanCompletion.lowerBound_le_totalCompletion
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:55:06.527076+00:00
-- url     : https://prove2.me/submissions/c9a28d40-b843-4245-9aa0-3cf191285ac4

import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound
open scoped BigOperators
open IgnallSchrage.MeanCompletion

private def wsum {n : ℕ} (a : Fin n → ℝ) (l : List (Fin n)) : ℝ :=
  ∑ q : Fin l.length, ((l.length : ℝ) - (q : ℝ)) * a l[q]

private lemma wsum_nil {n : ℕ} (a : Fin n → ℝ) : wsum a [] = 0 := by
  simp [wsum]

private lemma wsum_cons {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (l : List (Fin n)) :
    wsum a (j :: l) = ((l.length : ℝ) + 1) * a j + wsum a l := by
  unfold wsum
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [List.length_cons, Fin.val_zero, Nat.cast_zero, sub_zero,
    List.getElem_cons_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one, List.getElem_cons_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hget : (j :: l)[q.succ] = l[q] := rfl
  rw [hget]
  push_cast
  ring

private def tailTotal {n : ℕ} (a b : Fin n → ℝ) (t : ℝ × ℝ) : List (Fin n) → ℝ
  | [] => 0
  | j :: l => (appendJob a b t j).2 + tailTotal a b (appendJob a b t j) l

private lemma tail_T {n : ℕ} (a b : Fin n → ℝ) (l : List (Fin n)) (t : ℝ × ℝ) :
    (l.length : ℝ) * t.1 + wsum a l + (l.map b).sum ≤ tailTotal a b t l := by
  induction l generalizing t with
  | nil => simp [tailTotal, wsum_nil]
  | cons j l ih =>
    have hh := ih (appendJob a b t j)
    have hm : t.1 + a j ≤ max t.2 (t.1 + a j) := le_max_right _ _
    simp only [tailTotal, List.length_cons, Nat.cast_add, Nat.cast_one, wsum_cons,
      List.map_cons, List.sum_cons, appendJob] at *
    nlinarith

private lemma tail_S {n : ℕ} (a b : Fin n → ℝ) (l : List (Fin n)) (t : ℝ × ℝ) :
    (l.length : ℝ) * t.2 + wsum b l ≤ tailTotal a b t l := by
  induction l generalizing t with
  | nil => simp [tailTotal, wsum_nil]
  | cons j l ih =>
    have hh := ih (appendJob a b t j)
    have hm : t.2 ≤ max t.2 (t.1 + a j) := le_max_left _ _
    have hlen : 0 ≤ (l.length : ℝ) := by positivity
    simp only [tailTotal, List.length_cons, Nat.cast_add, Nat.cast_one, wsum_cons,
      appendJob] at *
    nlinarith

private lemma times_A {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) :
    (times a b J).1 = (J.map a).sum := by
  have hh : ∀ (l : List (Fin n)) (t : ℝ × ℝ),
      (l.foldl (appendJob a b) t).1 = t.1 + (l.map a).sum := by
    intro l
    induction l with
    | nil => intro t; simp
    | cons j l ih =>
      intro t
      simp [List.foldl_cons, ih, appendJob]
      ring
  simpa [times] using hh J (0,0)

private lemma Tval_formula {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n)) :
    Tval a b J l = (l.length : ℝ) * (J.map a).sum + wsum a l + (l.map b).sum := by
  simp only [Tval, wsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [← List.sum_ofFn]
  simp

private lemma Sval_formula {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n)) :
    Sval a b J l =
      (l.length : ℝ) * max (lastCompletion a b J) ((J.map a).sum + minUnscheduledA a J) +
      wsum b l := by
  simp [Sval, wsum, Finset.sum_add_distrib]

private lemma tail_mono {n : ℕ} (a b : Fin n → ℝ) (l : List (Fin n))
    (t u : ℝ × ℝ) (h1 : t.1 ≤ u.1) (h2 : t.2 ≤ u.2) :
    tailTotal a b t l ≤ tailTotal a b u l := by
  induction l generalizing t u with
  | nil => simp [tailTotal]
  | cons j l ih =>
    have hx : (appendJob a b t j).1 ≤ (appendJob a b u j).1 := by
      simp only [appendJob]
      linarith
    have hy : (appendJob a b t j).2 ≤ (appendJob a b u j).2 := by
      simp only [appendJob]
      gcongr
    exact add_le_add hy (ih _ _ hx hy)

private lemma Sval_le_tail {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n))
    (hl : l ∈ orderings J) :
    Sval a b J l ≤ tailTotal a b (times a b J) l := by
  cases l with
  | nil => simp [Sval, tailTotal]
  | cons j l =>
    have hj : j ∈ IgnallSchrage.Makespan.unscheduled J := by
      have hp := List.mem_permutations.mp (List.mem_toFinset.mp hl)
      have hm : j ∈ unscheduledList J := hp.mem_iff.mp (by simp)
      simpa [unscheduledList, IgnallSchrage.Makespan.unscheduled] using hm
    have hmin : minUnscheduledA a J ≤ a j := by
      have hne : (IgnallSchrage.Makespan.unscheduled J).Nonempty := ⟨j, hj⟩
      rw [minUnscheduledA, dif_pos hne]
      exact Finset.inf'_le _ hj
    let B := max (lastCompletion a b J) ((J.map a).sum + minUnscheduledA a J)
    have hb : B ≤ max (times a b J).2 ((times a b J).1 + a j) := by
      dsimp [B]
      rw [times_A]
      exact max_le_max le_rfl (add_le_add_right hmin _)
    have hh := tail_S a b l (appendJob a b (times a b J) j)
    rw [Sval_formula, wsum_cons]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, tailTotal, appendJob] at *
    have hlen : 0 ≤ (l.length : ℝ) := by positivity
    dsimp [B] at hb
    nlinarith

private lemma That_le_tail {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n))
    (hl : l ∈ orderings J) :
    That a b J ≤ tailTotal a b (times a b J) l := by
  apply (Finset.inf'_le _ hl).trans
  rw [Tval_formula, ← times_A a b J]
  exact tail_T a b l (times a b J)

private lemma Shat_le_tail {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n))
    (hl : l ∈ orderings J) :
    Shat a b J ≤ tailTotal a b (times a b J) l := by
  exact (Finset.inf'_le _ hl).trans (Sval_le_tail a b J l hl)

-- Prefix and scheduling-identification lemmas are developed below.

private lemma tailTotal_prefix {n : ℕ} (a b : Fin n → ℝ) (l : List (Fin n)) (t : ℝ × ℝ) :
    tailTotal a b t l =
      ∑ k ∈ Finset.range l.length, ((l.take (k + 1)).foldl (appendJob a b) t).2 := by
  induction l generalizing t with
  | nil => simp [tailTotal]
  | cons j l ih =>
    simp only [List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.foldl_cons, Nat.zero_add, List.take_zero,
      List.foldl_nil, tailTotal]
    rw [← ih]
    ring

private lemma node_eq_tail {n : ℕ} (a b : Fin n → ℝ) (l : List (Fin n)) :
    nodeCompletionSum a b l = tailTotal a b (0,0) l := by
  rw [tailTotal_prefix]
  rfl

private lemma tailTotal_append {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n)) (t : ℝ × ℝ) :
    tailTotal a b t (J ++ l) =
      tailTotal a b t J + tailTotal a b (J.foldl (appendJob a b) t) l := by
  induction J generalizing t with
  | nil => simp [tailTotal]
  | cons j J ih => simp [tailTotal, ih, add_assoc]

private lemma take_next {α : Type*} (l : List α) (k : ℕ) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons j l ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hkl : k < l.length := by simpa using hk
      simpa using congrArg (List.cons j) (ih k hkl)

private lemma prefix_A {n : ℕ} (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k < n) :
    (((List.ofFn σ).take (k + 1)).map a).sum =
      ∑ i ∈ Finset.Iic (⟨k,hk⟩ : Fin n), a (σ i) := by
  have hm : (((List.ofFn σ).take (k + 1)).map a) =
      (List.ofFn (fun i => a (σ i))).take (k + 1) := by
    rw [List.map_take, List.map_ofFn]
    rfl
  rw [hm, List.sum_take_ofFn]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic,
    Fin.le_iff_val_le_val, Fin.val_mk]
  omega

private lemma prefix_completion {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k ≤ n) :
    lastCompletion a b ((List.ofFn σ).take k) =
      JohnsonFlowShop.TwoStage.asapC2 a b σ k := by
  induction k with
  | zero => simp [lastCompletion, times, JohnsonFlowShop.TwoStage.asapC2]
  | succ k ih =>
    have hkn : k < n := by omega
    have hkl : k < (List.ofFn σ).length := by simpa using hkn
    rw [take_next _ _ hkl]
    simp only [lastCompletion, times, List.foldl_append, List.foldl_cons, List.foldl_nil,
      appendJob]
    rw [show ((List.ofFn σ).take k).foldl (appendJob a b) (0,0) =
      times a b ((List.ofFn σ).take k) from rfl]
    rw [times_A]
    have ha := prefix_A a σ k hkn
    have haa : (((List.ofFn σ).take k).map a).sum + a (σ ⟨k,hkn⟩) =
        ∑ i ∈ Finset.Iic (⟨k,hkn⟩ : Fin n), a (σ i) := by
      rw [take_next _ _ hkl] at ha
      simpa using ha
    have hb := ih (by omega)
    simp only [lastCompletion] at hb
    simp only [List.getElem_ofFn]
    rw [haa, hb, JohnsonFlowShop.TwoStage.asapC2, dif_pos hkn]
    rw [max_comm]

private lemma total_eq_node {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    totalCompletion a b σ = nodeCompletionSum a b (List.ofFn σ) := by
  unfold totalCompletion completionTime nodeCompletionSum
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply, List.length_ofFn]
  rw [Fin.sum_univ_eq_sum_range (fun k => JohnsonFlowShop.TwoStage.asapC2 a b σ (k+1))]
  apply Finset.sum_congr rfl
  intro k hk
  exact (prefix_completion a b σ (k+1) (by simp only [Finset.mem_range] at hk; omega)).symm

theorem solution {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (hr : 1 ≤ J.length) (hrn : J.length < n) (σ : Equiv.Perm (Fin n))
    (hσ : IgnallSchrage.Makespan.BeginsWith σ J) :
    lowerBound a b J ≤ totalCompletion a b σ := by
  classical
  rcases hσ with ⟨l, hfull⟩
  have hnd : (J ++ l).Nodup := by
    rw [hfull]
    exact List.nodup_ofFn_ofInjective σ.injective
  have hd := (List.nodup_append.mp hnd).2.2
  have hmem : ∀ j : Fin n, j ∈ l ↔ j ∉ J := by
    intro j
    constructor
    · intro hj hjJ
      exact hd j hjJ j hj rfl
    · intro hjn
      have hm : j ∈ J ++ l := by
        rw [hfull]
        exact List.mem_ofFn.mpr ⟨σ.symm j, by simp⟩
      simpa [List.mem_append, hjn] using hm
  have huns : (unscheduledList J).Nodup := by
    exact (List.nodup_finRange n).filter _
  have hp : l.Perm (unscheduledList J) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_append.mp hnd).2.1 huns).mpr
    intro j
    simpa [unscheduledList] using hmem j
  have hl : l ∈ orderings J :=
    List.mem_toFinset.mpr (List.mem_permutations.mpr hp)
  have ht := That_le_tail a b J l hl
  have hs := Shat_le_tail a b J l hl
  rw [total_eq_node, ← hfull, node_eq_tail, tailTotal_append]
  rw [lowerBound, node_eq_tail]
  exact add_le_add le_rfl (max_le ht hs)

#print axioms solution
