-- Prove2me | solution 1 for IgnallSchrage.MeanCompletion.lowerBound_eq_totalCompletion_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:26:24.252976+00:00
-- url     : https://prove2.me/submissions/7cc51a97-a12d-4619-994b-5c2f7569eaa9

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

theorem solution {n : ℕ} (a b : Fin n → ℝ)
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

#print axioms solution
