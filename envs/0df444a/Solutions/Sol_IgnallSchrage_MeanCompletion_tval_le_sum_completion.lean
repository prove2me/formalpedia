-- Prove2me | solution 1 for IgnallSchrage.MeanCompletion.tval_le_sum_completion
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:11:31.543745+00:00
-- url     : https://prove2.me/submissions/38e75a0e-9f53-4831-9b98-a5103c6f801d

import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound
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

private lemma weighted_prefix {α : Type*} (f : α → ℝ) (l : List α) :
    (∑ q : Fin l.length, ((l.length : ℝ)-(q : ℝ))*f l[q]) =
      ∑ q : Fin l.length, ((l.take (q.val+1)).map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.getElem_fin, Fin.val_zero, Nat.cast_zero, sub_zero,
      List.getElem_cons_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one,
      List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero]
    simp only [add_sub_add_right_eq_sub]
    rw [Finset.sum_add_distrib, ← ih]
    simp
    ring

private lemma tail_data {n : ℕ} (J : List (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : IgnallSchrage.Makespan.BeginsWith σ J) :
    let l := (List.ofFn σ).drop J.length
    J++l = List.ofFn σ ∧ l.Nodup ∧ l ∈ orderings J ∧
      l.toFinset = IgnallSchrage.Makespan.unscheduled J := by
  classical
  obtain ⟨l,hl⟩ := hσ
  have he : (List.ofFn σ).drop J.length = l := by rw [← hl]; simp
  rw [he]
  have hnd : (J++l).Nodup := hl ▸ List.nodup_ofFn.mpr σ.injective
  have hnot (i : Fin n) (hi : i ∈ l) : i ∉ J := by
    intro hj
    exact (List.nodup_append.mp hnd).2.2 i hj i hi rfl
  have hp : (List.finRange n).Perm (J++l) := by
    rw [hl, List.ofFn_eq_map]
    exact σ.map_finRange_perm.symm
  have hu : (unscheduledList J).Perm l := by
    have hh := hp.filter (fun i => decide (i ∉ J))
    have hz : J.filter (fun i => decide (i ∉ J)) = [] := by
      simp only [List.filter_eq_nil_iff]; intro i hi; simp [hi]
    have ht : l.filter (fun i => decide (i ∉ J)) = l := by
      apply List.filter_eq_self.mpr; intro i hi; simp [hnot i hi]
    simpa only [unscheduledList, List.filter_append, hz, ht, List.nil_append] using hh
  refine ⟨hl, (List.nodup_append.mp hnd).2.1, ?_, ?_⟩
  · exact List.mem_toFinset.mpr (List.mem_permutations.mpr hu.symm)
  · ext i
    simpa [unscheduledList, IgnallSchrage.Makespan.unscheduled] using hu.mem_iff.symm

private lemma tail_completion {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n))
    (σ : Equiv.Perm (Fin n)) (hl : J++l = List.ofFn σ) (q : Fin l.length) :
    completionTime a b σ l[q] = lastCompletion a b (J++l.take (q.val+1)) := by
  have hlen : J.length+l.length = n := by simpa using congrArg List.length hl
  have hk : J.length+q.val < n := by omega
  let k : Fin n := ⟨J.length+q.val,hk⟩
  have hj : σ k = l[q] := by
    have he := congrArg (fun t : List (Fin n) => t[J.length+q.val]?) hl
    simpa [List.getElem?_append, List.getElem?_ofFn, hk, k] using he.symm
  rw [← hj, completionTime, Equiv.symm_apply_apply]
  have ht : (List.ofFn σ).take (k.val+1) = J++l.take (q.val+1) := by
    rw [← hl, List.take_append]
    simp [k, List.take_of_length_le (show J.length ≤ J.length+q.val+1 by omega)]
    omega
  unfold lastCompletion
  rw [← ht, prefix_times a b σ (k.val+1) (by omega)]

private lemma sum_tail {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n))
    (σ : Equiv.Perm (Fin n)) (hl : J++l = List.ofFn σ) (hnd : l.Nodup)
    (hu : l.toFinset = IgnallSchrage.Makespan.unscheduled J) :
    (∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i) =
      ∑ q : Fin l.length, lastCompletion a b (J++l.take (q.val+1)) := by
  rw [← hu, List.sum_toFinset _ hnd, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro q hq
  exact tail_completion a b J l σ hl q

private lemma last_le {n : ℕ} (a b : Fin n → ℝ) (P : List (Fin n)) (j : Fin n) :
    (P.map a).sum+a j+b j ≤ lastCompletion a b (P++[j]) := by
  simp only [lastCompletion, times_append, appendJob, times_first]
  linarith [le_max_right (times a b P).2 ((P.map a).sum+a j)]

theorem solution {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (hr : 1 ≤ J.length) (hrn : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : IgnallSchrage.Makespan.BeginsWith σ J) :
    Tval a b J ((List.ofFn σ).drop J.length) ≤ ∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i ∧
    That a b J ≤ ∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i := by
  classical
  let l := (List.ofFn σ).drop J.length
  obtain ⟨hl, hnd, ho, hu⟩ := tail_data J σ hσ
  have hb : Tval a b J l ≤ ∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i := by
    rw [sum_tail a b J l σ hl hnd hu]
    unfold Tval
    simp only [Finset.sum_add_distrib]
    rw [weighted_prefix a l]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q hq
    have hi : q.val < l.length := q.isLt
    rw [List.take_succ_eq_append_getElem hi]
    have hh := last_le a b (J++l.take q.val) l[q]
    simpa [List.map_append, List.sum_append, List.append_assoc, add_assoc] using hh
  exact ⟨hb, (Finset.inf'_le (Tval a b J) ho).trans hb⟩

#print axioms solution
