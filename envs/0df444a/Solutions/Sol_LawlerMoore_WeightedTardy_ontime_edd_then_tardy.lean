-- Prove2me | solution 1 for LawlerMoore.WeightedTardy.ontime_edd_then_tardy
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:11:35.376176+00:00
-- url     : https://prove2.me/submissions/eb0d78b8-7926-4ebb-a6fa-59ed7c8142a3

import Mathlib
import Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy



namespace LawlerMoore.WeightedTardy

open MooreLateJobs.Shared MooreLateJobs.NumLate

section sched

theorem lm_ct_def {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (l : List ι) (j : ι) :
    completionTime t l j = ((l.take (l.idxOf j + 1)).map t).sum := rfl

theorem lm_ct_append_left {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (A B : List ι) (j : ι)
    (hj : j ∈ A) : completionTime t (A ++ B) j = completionTime t A j := by
  simp only [lm_ct_def, List.idxOf_append_of_mem hj]
  rw [List.take_append_of_le_length]
  have := List.idxOf_lt_length_of_mem hj
  omega

theorem lm_mem_lateSet {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (l : List ι) (j : ι) :
    j ∈ lateSet t D l ↔ j ∈ l ∧ D j < completionTime t l j := by
  simp [lateSet]

theorem lm_ct_split {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s u : List ι) (j : ι)
    (hnd : (s ++ j :: u).Nodup) :
    completionTime t (s ++ j :: u) j = (s.map t).sum + t j := by
  have hj : j ∉ s := by
    intro h
    have := List.nodup_append.1 hnd
    exact this.2.2 j h j (List.mem_cons_self) rfl
  have e : (s ++ j :: u).take (s.length + 1) = s ++ [j] := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  rw [lm_ct_def, List.idxOf_append_of_notMem hj, List.idxOf_cons_self, Nat.add_zero, e]
  simp

theorem lm_key {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (l : List ι)
    (hl : l.Nodup) (X : Finset ι) (hX : X.Nonempty) (hXl : ∀ i ∈ X, i ∈ l) :
    ∃ m ∈ X, ∑ i ∈ X, t i ≤ completionTime t l m := by
  obtain ⟨m, hmX, hmax⟩ := Finset.exists_max_image X (fun i => l.idxOf i) hX
  refine ⟨m, hmX, ?_⟩
  have hsub : X ⊆ (l.take (l.idxOf m + 1)).toFinset := by
    intro i hi
    rw [List.mem_toFinset]
    have hil := hXl i hi
    have h1 : l.idxOf i < l.length := List.idxOf_lt_length_of_mem hil
    have h2 : l.idxOf i < l.idxOf m + 1 := by have := hmax i hi; omega
    rw [List.mem_iff_getElem]
    refine ⟨l.idxOf i, by simp [List.length_take]; omega, ?_⟩
    simp [List.getElem_take]
  calc ∑ i ∈ X, t i ≤ ∑ i ∈ (l.take (l.idxOf m + 1)).toFinset, t i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ht i)
    _ = ((l.take (l.idxOf m + 1)).map t).sum :=
        List.sum_toFinset t ((hl.sublist (List.take_sublist _ _)))
    _ = completionTime t l m := rfl


theorem lm_edd_core {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    ∃ E : List (Fin n),
      E.Nodup ∧
      (∀ j, j ∈ E ↔ j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) l) ∧
      E.Pairwise (fun i j => d i ≤ d j) ∧
      ∀ L : List (Fin n), IsSchedule Finset.univ (E ++ L) →
        (∀ j ∈ E, j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) (E ++ L)) ∧
        weightedTardy a' d p (E ++ L) ≤ weightedTardy a' d p l := by
  set t : Fin n → ℝ := fun i => (a' i : ℝ) with ht_def
  set D : Fin n → ℝ := fun i => (d i : ℝ) with hD_def
  have ht0 : ∀ i, 0 ≤ t i := fun i => Nat.cast_nonneg _
  have hmem : ∀ j, j ∈ l := fun j => (hl.2 j).2 (Finset.mem_univ j)
  set A : List (Fin n) := l.filter (fun j => decide (j ∉ lateSet t D l)) with hA
  set E : List (Fin n) := A.mergeSort (fun i j => decide (d i ≤ d j)) with hE
  have hperm : E.Perm A := List.mergeSort_perm _ _
  have hAnd : A.Nodup := hl.1.filter _
  have hEnd : E.Nodup := hperm.nodup_iff.2 hAnd
  have hEmem : ∀ j, j ∈ E ↔ j ∉ lateSet t D l := by
    intro j
    rw [hperm.mem_iff, hA, List.mem_filter]
    simp [hmem j]
  have hEpw : E.Pairwise (fun i j => d i ≤ d j) := by
    have := List.pairwise_mergeSort (le := fun i j => decide (d i ≤ d j))
      (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) A
    simpa using this
  have hEok : ∀ j ∈ E, completionTime t E j ≤ D j := by
    intro j hj
    obtain ⟨s, u, hsu⟩ := List.append_of_mem hj
    have hnd : (s ++ j :: u).Nodup := hsu ▸ hEnd
    have hjs : j ∉ s := by
      intro h
      have := List.nodup_append.1 hnd
      exact this.2.2 j h j (List.mem_cons_self) rfl
    have hsnd : s.Nodup := (List.nodup_append.1 hnd).1
    rw [hsu, lm_ct_split t s u j hnd]
    set X : Finset (Fin n) := insert j s.toFinset with hX
    have hsum : ∑ i ∈ X, t i = (s.map t).sum + t j := by
      rw [hX, Finset.sum_insert (by simpa using hjs), List.sum_toFinset t hsnd]
      ring
    obtain ⟨m, hmX, hm⟩ := lm_key t ht0 l hl.1 X ⟨j, Finset.mem_insert_self _ _⟩
      (fun i _ => hmem i)
    have hmE : m ∈ E := by
      rw [hsu]
      rcases Finset.mem_insert.1 hmX with h | h
      · rw [h]; simp
      · simp at h; simp [h]
    have hmon : m ∉ lateSet t D l := (hEmem m).1 hmE
    have hmct : completionTime t l m ≤ D m := by
      rw [lm_mem_lateSet] at hmon
      push_neg at hmon
      exact hmon (hmem m)
    have hdm : d m ≤ d j := by
      rcases Finset.mem_insert.1 hmX with h | h
      · rw [h]
      · have hs : m ∈ s := by simpa using h
        have := hEpw
        rw [hsu, List.pairwise_append] at this
        exact this.2.2 m hs j (List.mem_cons_self)
    rw [← hsum]
    calc _ ≤ completionTime t l m := hm
      _ ≤ D m := hmct
      _ ≤ D j := by simp only [hD_def]; exact_mod_cast hdm
  refine ⟨E, hEnd, hEmem, hEpw, fun L _ => ?_⟩
  have hon : ∀ j ∈ E, j ∉ lateSet t D (E ++ L) := by
    intro j hj
    rw [lm_mem_lateSet, lm_ct_append_left t E L j hj]
    push_neg
    intro _
    exact hEok j hj
  refine ⟨hon, ?_⟩
  unfold weightedTardy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    by_contra hnot
    exact hon j ((hEmem j).2 hnot) hj
  · intro i _ _; exact hp i

end sched
end LawlerMoore.WeightedTardy

open LawlerMoore.WeightedTardy
open MooreLateJobs.Shared MooreLateJobs.NumLate

theorem solution {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    ∃ E : List (Fin n),
      E.Nodup ∧
      (∀ j, j ∈ E ↔ j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) l) ∧
      E.Pairwise (fun i j => d i ≤ d j) ∧
      ∀ L : List (Fin n), IsSchedule Finset.univ (E ++ L) →
        (∀ j ∈ E, j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) (E ++ L)) ∧
        weightedTardy a' d p (E ++ L) ≤ weightedTardy a' d p l := by
  exact lm_edd_core a' d p hp l hl
