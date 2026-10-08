-- Prove2me | solution 1 for IgnallSchrage.MeanCompletion.branch_and_bound_optimal
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:05:48.177206+00:00
-- url     : https://prove2.me/submissions/79be8cb2-73c5-4a9e-8275-4354a6d8dc5f

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure
namespace BoundSupport
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

private theorem bound {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (σ : Equiv.Perm (Fin n))
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



end BoundSupport
namespace TerminalSupport
open IgnallSchrage.MeanCompletion
open JohnsonFlowShop.TwoStage

private lemma times_append {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) (j : Fin n) :
    times a b (J ++ [j]) = appendJob a b (times a b J) j := by
  simp [times, List.foldl_append]

private lemma times_first {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) :
    (times a b J).1 = (J.map a).sum := by
  induction J using List.reverseRecOn with
  | nil => simp [times]
  | append_singleton J j ih => simp [times_append, appendJob, ih]

private lemma prefix_times {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (m : ℕ) (hm : m ≤ n) :
    times a b ((List.ofFn σ).take m) =
      (∑ i ∈ (Finset.univ.filter (fun i : Fin n => i.val < m)), a (σ i), asapC2 a b σ m) := by
  induction m with
  | zero => simp [times, asapC2]
  | succ m ih =>
    have hmn : m < n := by omega
    let k : Fin n := ⟨m, hmn⟩
    have hi : m < (List.ofFn σ).length := by simpa
    have hset : (Finset.univ.filter (fun i : Fin n => i.val < m+1)) =
        insert k (Finset.univ.filter (fun i : Fin n => i.val < m)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h; by_cases he : i.val = m
        · left; exact Fin.ext he
        · right; omega
      · rintro (rfl | h) <;> simp_all [k] <;> omega
    have hiic : Finset.Iic k = Finset.univ.filter (fun i : Fin n => i.val < m+1) := by
      ext i; simp [Fin.le_iff_val_le_val, k]
    rw [List.take_succ_eq_append_getElem hi]
    simp only [List.getElem_ofFn, times_append, ih (by omega)]
    simp only [appendJob, asapC2, dif_pos hmn]
    rw [← hiic, hiic, hset, Finset.sum_insert (by simp [k])]
    simp only [k]
    congr 1
    · ring
    · rw [max_comm]
      congr 2
      ring

private lemma full_sum {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    nodeCompletionSum a b (List.ofFn σ) = totalCompletion a b σ := by
  unfold nodeCompletionSum totalCompletion completionTime
  simp only [List.length_ofFn]
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  unfold lastCompletion
  rw [prefix_times a b σ (i.val+1) (by omega)]

private lemma node_sum_append {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) (j : Fin n) :
    nodeCompletionSum a b (J ++ [j]) = nodeCompletionSum a b J + lastCompletion a b (J ++ [j]) := by
  unfold nodeCompletionSum
  simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    rw [List.take_append_of_le_length (by have := Finset.mem_range.mp hm; omega)]
  · rw [show J.length + 1 = (J ++ [j]).length by simp, List.take_length]

private theorem terminal {n : ℕ} (a b : Fin n → ℝ)
    (J : List (Fin n)) (hJ : J.length + 1 = n) (σ : Equiv.Perm (Fin n))
    (hσ : IgnallSchrage.Makespan.BeginsWith σ J) :
    lowerBound a b J = totalCompletion a b σ := by
  classical
  obtain ⟨l, hl⟩ := hσ
  have hlen : l.length = 1 := by have := congrArg List.length hl; simp at this; omega
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hnd : (J ++ [j]).Nodup := hl ▸ List.nodup_ofFn.mpr σ.injective
  have hj : j ∉ J := by
    intro hj
    exact (List.nodup_append.mp hnd).2.2 j hj j (by simp) rfl
  have hp : (List.finRange n).Perm (J ++ [j]) := by
    rw [hl, List.ofFn_eq_map]
    exact σ.map_finRange_perm.symm
  have hu : unscheduledList J = [j] := by
    have hh := hp.filter (fun i => decide (i ∉ J))
    have hz : J.filter (fun i => decide (i ∉ J)) = [] := by
      simp only [List.filter_eq_nil_iff]; intro i hi; simp [hi]
    simp only [List.filter_append, hz, List.nil_append] at hh
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, hj, not_false_eq_true, if_true] at hh
    exact List.perm_singleton.mp hh
  have ho : orderings J = {[j]} := by
    ext l
    simp [orderings, hu, List.mem_permutations, List.perm_singleton]
  have hf : (J.map a).sum = (times a b J).1 := (times_first a b J).symm
  have ht : That a b J = (J.map a).sum + a j + b j := by
    simp [That, ho, Tval, Fin.sum_univ_one]
  have huns : IgnallSchrage.Makespan.unscheduled J = {j} := by
    ext i
    have hm : i ∈ unscheduledList J ↔ i ∉ J := by simp [unscheduledList]
    simpa [IgnallSchrage.Makespan.unscheduled, hu] using hm.symm
  have hmin : minUnscheduledA a J = a j := by simp [minUnscheduledA, huns]
  have hs : Shat a b J = max (lastCompletion a b J) ((J.map a).sum + a j) + b j := by
    simp [Shat, ho, Sval, Fin.sum_univ_one, hmin]
  have hc : lastCompletion a b (J ++ [j]) =
      max (lastCompletion a b J) ((J.map a).sum + a j) + b j := by
    simp [lastCompletion, times_append, appendJob, times_first]
  rw [← full_sum a b σ, ← hl, node_sum_append, lowerBound, ht, hs]
  rw [max_eq_right (by linarith [le_max_right (lastCompletion a b J) ((J.map a).sum + a j)]), hc]



end TerminalSupport
open IgnallSchrage.Makespan
set_option autoImplicit false

private def Good {n : ℕ} (P : List (Fin n)) : Prop := P.Nodup ∧ P.length+1 ≤ n
private def Covers {n : ℕ} (L : List (List (Fin n))) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∃ P ∈ L, BeginsWith σ P
private def Ranked {n : ℕ} (LB : List (Fin n) → ℝ) (L : List (List (Fin n))) : Prop :=
  L.Pairwise (fun P Q => LB P ≤ LB Q)

private lemma mem_insert {n : ℕ} (LB : List (Fin n) → ℝ) (x y : List (Fin n))
    (L : List (List (Fin n))) :
    y ∈ insertNode LB x L ↔ y = x ∨ y ∈ L := by
  induction L with
  | nil => simp [insertNode, eq_comm]
  | cons z zs ih =>
    simp only [insertNode]
    split_ifs <;> simp [ih, or_assoc, or_left_comm]

private lemma mem_fold {n : ℕ} (LB : List (Fin n) → ℝ)
    (C L : List (List (Fin n))) (y : List (Fin n)) :
    y ∈ C.foldl (fun L x => insertNode LB x L) L ↔ y ∈ C ∨ y ∈ L := by
  induction C generalizing L with
  | nil => simp
  | cons x xs ih => simp [ih, mem_insert, or_assoc, or_left_comm]

private lemma insert_ranked {n : ℕ} (LB : List (Fin n) → ℝ) (x : List (Fin n))
    (L : List (List (Fin n))) (hL : Ranked LB L) : Ranked LB (insertNode LB x L) := by
  induction L with
  | nil => simp [Ranked, insertNode]
  | cons y ys ih =>
    obtain ⟨hy,hys⟩ := List.pairwise_cons.mp hL
    simp only [insertNode]
    split_ifs with h
    · apply List.pairwise_cons.mpr
      refine ⟨?_,hL⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h
      · exact h.trans (hy z hz)
    · apply List.pairwise_cons.mpr
      refine ⟨?_,ih hys⟩
      intro z hz
      rcases (mem_insert LB x z ys).mp hz with rfl | hz
      · exact (lt_of_not_ge h).le
      · exact hy z hz

private lemma fold_ranked {n : ℕ} (LB : List (Fin n) → ℝ)
    (C L : List (List (Fin n))) (hL : Ranked LB L) :
    Ranked LB (C.foldl (fun L x => insertNode LB x L) L) := by
  induction C generalizing L with
  | nil => exact hL
  | cons x xs ih => exact ih _ (insert_ranked LB x L hL)

private lemma children_good {n : ℕ} (P : List (Fin n)) (hP : Good P) (hT : ¬ IsTerminal P) :
    ∀ Q ∈ children P, Good Q := by
  intro Q hQ
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hQ
  have hj' : j ∉ P := by simpa using (List.mem_filter.mp hj).2
  refine ⟨by simpa using hP.1.concat hj',?_⟩
  have hh := hP.2
  simp only [IsTerminal] at hT
  simp only [List.length_append, List.length_singleton]
  omega

private lemma child_prefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : List (Fin n))
    (hP : Good P) (hT : ¬ IsTerminal P) (hσ : BeginsWith σ P) :
    ∃ Q ∈ children P, BeginsWith σ Q := by
  obtain ⟨l,hl⟩ := hσ
  cases l with
  | nil =>
    have he := congrArg List.length hl
    simp only [List.append_nil, List.length_ofFn] at he
    have := hP.2; omega
  | cons j l =>
    have hnd : (P++j::l).Nodup := hl ▸ List.nodup_ofFn.mpr σ.injective
    have hj : j ∉ P := by
      intro hj
      exact (List.nodup_append.mp hnd).2.2 j hj j (by simp) rfl
    refine ⟨P++[j], List.mem_map.mpr ⟨j,?_,rfl⟩,l,?_⟩
    · simp [hj]
    · simpa only [List.append_assoc, List.singleton_append] using hl

private lemma step_invariants {n : ℕ} (LB : List (Fin n) → ℝ) (L : List (List (Fin n)))
    (hg : ∀ P ∈ L, Good P) (hc : Covers L) (hr : Ranked LB L) :
    (∀ P ∈ step LB L, Good P) ∧ Covers (step LB L) ∧ Ranked LB (step LB L) := by
  cases L with
  | nil => exact ⟨by simp [step],hc,hr⟩
  | cons P rest =>
    by_cases ht : IsTerminal P
    · simpa [step,ht] using And.intro hg (And.intro hc hr)
    · have hp := hg P (by simp)
      simp only [step, if_neg ht]
      refine ⟨?_,?_,fold_ranked LB _ _ (List.pairwise_cons.mp hr).2⟩
      · intro Q hQ
        rcases (mem_fold LB _ _ Q).mp hQ with hQ | hQ
        · exact children_good P hp ht Q hQ
        · exact hg Q (by simp [hQ])
      · intro σ
        obtain ⟨Q,hQ,hσ⟩ := hc σ
        rcases List.mem_cons.mp hQ with rfl | hQ
        · obtain ⟨R,hR,hσ⟩ := child_prefix σ Q hp ht hσ
          exact ⟨R,(mem_fold LB _ _ R).mpr (Or.inl hR),hσ⟩
        · exact ⟨Q,(mem_fold LB _ _ Q).mpr (Or.inr hQ),hσ⟩

private lemma run_invariants {n : ℕ} (hn : 1 ≤ n) (LB : List (Fin n) → ℝ) (k : ℕ) :
    (∀ P ∈ run LB k, Good P) ∧ Covers (run LB k) ∧ Ranked LB (run LB k) := by
  induction k with
  | zero =>
    simp only [run, Function.iterate_zero, id_eq]
    refine ⟨?_,?_,?_⟩
    · intro P hP; simp only [List.mem_singleton] at hP; subst P; exact ⟨by simp,hn⟩
    · intro σ; exact ⟨[],by simp,by simp [BeginsWith]⟩
    · simp [Ranked]
  | succ k ih =>
    simp only [run, Function.iterate_succ_apply'] at ih ⊢
    exact step_invariants LB _ ih.1 ih.2.1 ih.2.2

private def weight {n : ℕ} (P : List (Fin n)) : ℕ := (n+1)^(n-P.length)
private def potential {n : ℕ} (L : List (List (Fin n))) : ℕ := (L.map weight).sum

private lemma potential_insert {n : ℕ} (LB : List (Fin n) → ℝ) (x : List (Fin n))
    (L : List (List (Fin n))) : potential (insertNode LB x L) = weight x+potential L := by
  induction L with
  | nil => simp [potential,insertNode]
  | cons y ys ih =>
    simp only [insertNode]
    split_ifs <;> simp [potential] at ih ⊢ <;> omega

private lemma potential_fold {n : ℕ} (LB : List (Fin n) → ℝ)
    (C L : List (List (Fin n))) :
    potential (C.foldl (fun L x => insertNode LB x L) L) = potential C+potential L := by
  induction C generalizing L with
  | nil => simp [potential]
  | cons x xs ih =>
    rw [List.foldl_cons, ih, potential_insert]
    simp [potential]
    omega

private lemma children_weight {n : ℕ} (P : List (Fin n)) (hP : Good P) (hT : ¬ IsTerminal P) :
    potential (children P) < weight P := by
  let U := (List.finRange n).filter (fun j => decide (j ∉ P))
  have he : potential (children P) = U.length*(n+1)^(n-(P.length+1)) := by
    unfold potential children
    change (((U.map (fun j => P++[j])).map weight).sum) = _
    simp only [List.map_map, Function.comp_def, weight, List.length_append, List.length_singleton]
    simp
  have hlen : U.length ≤ n := (List.length_filter_le _ _).trans (by simp)
  have hP' := hP.2
  have hexp : n-P.length = n-(P.length+1)+1 := by omega
  rw [he, weight, hexp, pow_succ]
  have hpow : 0 < (n+1)^(n-(P.length+1)) := pow_pos (by omega) _
  nlinarith

private lemma terminate {n : ℕ} (LB : List (Fin n) → ℝ) (L : List (List (Fin n)))
    (hg : ∀ P ∈ L, Good P) (hc : Covers L) (hr : Ranked LB L) :
    ∃ k P, ((step LB)^[k] L).head? = some P ∧ IsTerminal P := by
  suffices hh : ∀ r L, potential L = r →
    (∀ P ∈ L, Good P) → Covers L → Ranked LB L →
    ∃ k P, ((step LB)^[k] L).head? = some P ∧ IsTerminal P from hh _ L rfl hg hc hr
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro L he hg hc hr
    obtain ⟨Q,hQ,_⟩ := hc (Equiv.refl _)
    cases L with
    | nil => simp at hQ
    | cons P rest =>
      by_cases ht : IsTerminal P
      · exact ⟨0,P,by simp,ht⟩
      · have hp := hg P (by simp)
        have hd : potential (step LB (P::rest)) < potential (P::rest) := by
          rw [step, if_neg ht, potential_fold]
          have := children_weight P hp ht
          simp only [potential,List.map_cons,List.sum_cons] at *
          omega
        obtain ⟨hg',hc',hr'⟩ := step_invariants LB _ hg hc hr
        obtain ⟨k,R,hR,hT⟩ := ih _ (by omega) _ rfl hg' hc' hr'
        exact ⟨k+1,R,by simpa only [Function.iterate_succ_apply] using hR,hT⟩

private lemma extension {n : ℕ} (P : List (Fin n)) (hP : Good P) :
    ∃ σ : Equiv.Perm (Fin n), BeginsWith σ P := by
  classical
  let l := P++IgnallSchrage.MeanCompletion.unscheduledList P
  have hnd : l.Nodup := by
    refine List.nodup_append.mpr ⟨hP.1,(List.nodup_finRange n).filter _,?_⟩
    intro i hi j hj hij
    subst j
    have : i ∉ P := by simpa [IgnallSchrage.MeanCompletion.unscheduledList] using (List.mem_filter.mp hj).2
    exact this hi
  have hp : l.Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange n)).mpr
    intro j
    simp [l,IgnallSchrage.MeanCompletion.unscheduledList]
    exact em _
  have hl : l.length = n := by simpa using hp.length_eq
  let f : Fin n → Fin n := fun i => l[i.val]'(by rw [hl]; exact i.isLt)
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact hnd.getElem_inj_iff.mp he
  let σ := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,rfl⟩)
  have he : List.ofFn σ = l := by
    apply List.ext_getElem
    · simp [hl]
    · intro i hi hj
      simp [σ,f]
  exact ⟨σ,IgnallSchrage.MeanCompletion.unscheduledList P,he.symm⟩

open IgnallSchrage.MeanCompletion
theorem solution {n : ℕ} (hn : 1 ≤ n) (a b : Fin n → ℝ) :
    (∃ k P, (IgnallSchrage.Makespan.run (lowerBound a b) k).head? = some P ∧ IgnallSchrage.Makespan.IsTerminal P) ∧
    ∀ k P, (IgnallSchrage.Makespan.run (lowerBound a b) k).head? = some P → IgnallSchrage.Makespan.IsTerminal P →
      ∃ σstar : Equiv.Perm (Fin n), IgnallSchrage.Makespan.BeginsWith σstar P ∧
        ∀ σ : Equiv.Perm (Fin n), totalCompletion a b σstar ≤ totalCompletion a b σ  := by
  classical
  have hi (k : ℕ) := run_invariants hn (lowerBound a b) k
  constructor
  · obtain ⟨k,P,hP,hT⟩ := terminate (lowerBound a b) [[]]
      (by intro P hP; simp only [List.mem_singleton] at hP; subst P; exact ⟨by simp,hn⟩)
      (by intro σ; exact ⟨[],by simp,by simp [Covers,BeginsWith]⟩)
      (by simp [Ranked])
    exact ⟨k,P,hP,hT⟩
  · intro k P hP hT
    have hmem : P ∈ run (lowerBound a b) k := by
      obtain ⟨rest,he⟩ := List.head?_eq_some_iff.mp hP
      rw [he]; simp
    have hp := (hi k).1 P hmem
    obtain ⟨σstar,hσstar⟩ := extension P hp
    refine ⟨σstar,hσstar,?_⟩
    intro σ
    obtain ⟨Q,hQ,hσ⟩ := (hi k).2.1 σ
    have hbound := BoundSupport.bound a b Q σ hσ
    have hmin : lowerBound a b P ≤ lowerBound a b Q := by
      obtain ⟨rest,he⟩ := List.head?_eq_some_iff.mp hP
      rw [he] at hQ
      have hr := (hi k).2.2
      rw [he] at hr
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact le_rfl
      · exact (List.pairwise_cons.mp hr).1 Q hQ
    rw [← TerminalSupport.terminal a b P hT σstar hσstar]
    exact hmin.trans hbound
#print axioms solution
