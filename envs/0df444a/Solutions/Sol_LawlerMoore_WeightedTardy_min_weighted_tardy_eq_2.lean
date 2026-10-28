-- Prove2me | solution 2 for LawlerMoore.WeightedTardy.min_weighted_tardy_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:48:25.194968+00:00
-- url     : https://prove2.me/submissions/e617afb9-f590-46f9-86ef-42eac639d05b

import Mathlib
import Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy
import Definitions.Def_LawlerMoore_WeightedTardy_eq3
import Theorems.Thm_LawlerMoore_WeightedTardy_eq3_value

-- carved verbatim out of submission 46c103f2-12ce-459a-8c1e-0e72edafcd7f, lines 673-679

section
open LawlerMoore
open LawlerMoore.WeightedTardy
open MooreLateJobs.Shared MooreLateJobs.NumLate
open Finset
variable {n : ℕ}

theorem lm_T (a' : Fin n → ℕ) (x : Fin n → Bool) (j : ℕ) (k : Fin n) (hk : k.val = j)
    (hx : ∀ i : Fin n, j + 1 ≤ i.val → x i = false) :
    ∑ i, a' i * (x i).toNat = ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i ≤ k
  · simp [h]
  · have : j + 1 ≤ i.val := by rw [Fin.le_def] at h; omega
    simp [h, hx i this]

end

section
open LawlerMoore
open LawlerMoore.WeightedTardy
open MooreLateJobs.Shared MooreLateJobs.NumLate
open Finset

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

theorem lm_sum_dec {ι : Type*} (S : Finset ι) (c : ι → ℕ) (q : ι → Prop) [DecidablePred q] :
    ∑ i ∈ S, c i * (decide (q i)).toNat = ∑ i ∈ S.filter q, c i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i <;> simp [h]

theorem lm_sum_dec_real {ι : Type*} (S : Finset ι) (c : ι → ℝ) (q : ι → Prop) [DecidablePred q] :
    ∑ i ∈ S, c i * ((decide (q i)).toNat : ℝ) = ∑ i ∈ S.filter q, c i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i <;> simp [h]

theorem lm_part1 {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) (hd : Monotone d)
    (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    ∃ x : Fin n → Bool, PrefixFeasible a' d x ∧
      (∑ j, p j) - knapValue p x ≤ weightedTardy a' d p l := by
  set t : Fin n → ℝ := fun i => (a' i : ℝ) with ht_def
  set D : Fin n → ℝ := fun i => (d i : ℝ) with hD_def
  have ht0 : ∀ i, 0 ≤ t i := fun i => Nat.cast_nonneg _
  have hmem : ∀ j, j ∈ l := fun j => (hl.2 j).2 (Finset.mem_univ j)
  set late := lateSet t D l with hlate
  refine ⟨fun j => decide (j ∉ late), ?_, ?_⟩
  · intro k
    set X : Finset (Fin n) := Finset.univ.filter (fun i => i ≤ k ∧ i ∉ late) with hX
    have hsumX : ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), a' i * (decide (i ∉ late)).toNat
        = ∑ i ∈ X, a' i := by
      rw [lm_sum_dec, Finset.filter_filter]
    rw [hsumX]
    by_cases hXe : X = ∅
    · rw [hXe]; simp
    · obtain ⟨m, hmX, hm⟩ := lm_key t ht0 l hl.1 X (Finset.nonempty_iff_ne_empty.2 hXe)
        (fun i _ => hmem i)
      have hmX' := (Finset.mem_filter.1 hmX).2
      have hmct : completionTime t l m ≤ D m := by
        have := hmX'.2
        rw [hlate, lm_mem_lateSet] at this
        push_neg at this
        exact this (hmem m)
      have hdm : d m ≤ d k := hd hmX'.1
      have : ∑ i ∈ X, t i ≤ (d k : ℝ) :=
        le_trans hm (le_trans hmct (by simp only [hD_def]; exact_mod_cast hdm))
      have h2 : ((∑ i ∈ X, a' i : ℕ) : ℝ) ≤ (d k : ℝ) := by
        push_cast; exact this
      exact_mod_cast h2
  · have h1 : knapValue p (fun j => decide (j ∉ late)) = ∑ j ∈ Finset.univ.filter (fun j => j ∉ late), p j := by
      unfold knapValue
      exact lm_sum_dec_real _ _ _
    have h2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ late) p
    have h3 : Finset.univ.filter (fun j => j ∈ late) = late := by ext; simp
    unfold weightedTardy
    rw [h1]
    rw [h3] at h2
    simp only [← hlate] at *
    linarith

theorem lm_sum_bool {ι : Type*} (S : Finset ι) (c : ι → ℕ) (y : ι → Bool) :
    ∑ i ∈ S, c i * (y i).toNat = ∑ i ∈ S.filter (fun i => y i = true), c i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases h : y i <;> simp

theorem lm_sum_bool_real {ι : Type*} (S : Finset ι) (c : ι → ℝ) (y : ι → Bool) :
    ∑ i ∈ S, c i * ((y i).toNat : ℝ) = ∑ i ∈ S.filter (fun i => y i = true), c i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases h : y i <;> simp

theorem lm_part2 {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (x : Fin n → Bool) (hx : PrefixFeasible a' d x) :
    ∃ l : List (Fin n), IsSchedule Finset.univ l ∧
      weightedTardy a' d p l ≤ (∑ j, p j) - knapValue p x := by
  set t : Fin n → ℝ := fun i => (a' i : ℝ) with ht_def
  set D : Fin n → ℝ := fun i => (d i : ℝ) with hD_def
  set E : List (Fin n) := (List.finRange n).filter (fun j => x j) with hE
  set F : List (Fin n) := (List.finRange n).filter (fun j => !x j) with hF
  have hperm : (E ++ F).Perm (List.finRange n) := List.filter_append_perm _ _
  have hsch : IsSchedule Finset.univ (E ++ F) :=
    ⟨hperm.nodup_iff.2 (List.nodup_finRange n), fun j => by simp [hperm.mem_iff]⟩
  have hEs : E.Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _
  have hEnd : E.Nodup := (List.nodup_finRange n).filter _
  have hEmem : ∀ j, j ∈ E ↔ x j = true := by intro j; simp [hE]
  have hEok : ∀ j ∈ E, completionTime t (E ++ F) j ≤ D j := by
    intro j hj
    rw [lm_ct_append_left t E F j hj]
    obtain ⟨s, u, hsu⟩ := List.append_of_mem hj
    have hnd : (s ++ j :: u).Nodup := hsu ▸ hEnd
    have hsnd : s.Nodup := (List.nodup_append.1 hnd).1
    have hjs : j ∉ s := by
      intro h
      have := List.nodup_append.1 hnd
      exact this.2.2 j h j (List.mem_cons_self) rfl
    have hpw := hEs
    rw [hsu, List.pairwise_append] at hpw
    have hlts : ∀ i ∈ s, i < j := fun i hi => hpw.2.2 i hi j (List.mem_cons_self)
    have hltu : ∀ i ∈ u, j < i := fun i hi => (List.pairwise_cons.1 hpw.2.1).1 i hi
    rw [hsu, lm_ct_split t s u j hnd]
    have hY : insert j s.toFinset = Finset.univ.filter (fun i => i ≤ j ∧ x i = true) := by
      ext i
      simp only [Finset.mem_insert, List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | hi)
        · exact ⟨le_rfl, (hEmem i).1 hj⟩
        · refine ⟨le_of_lt (hlts i hi), (hEmem i).1 ?_⟩
          rw [hsu]; simp [hi]
      · rintro ⟨hij, hxi⟩
        have : i ∈ s ++ j :: u := by rw [← hsu]; exact (hEmem i).2 hxi
        rcases List.mem_append.1 this with h | h
        · right; exact h
        · rcases List.mem_cons.1 h with h | h
          · left; exact h
          · exact absurd (hltu i h) (not_lt.2 hij)
    have hsum : (s.map t).sum + t j = ∑ i ∈ insert j s.toFinset, t i := by
      rw [Finset.sum_insert (by simpa using hjs), List.sum_toFinset t hsnd]
      ring
    have h1 := hx j
    rw [lm_sum_bool, Finset.filter_filter] at h1
    rw [hsum, hY]
    have h2 : ((∑ i ∈ Finset.univ.filter (fun i => i ≤ j ∧ x i = true), a' i : ℕ) : ℝ) ≤ (d j : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact h2
  refine ⟨E ++ F, hsch, ?_⟩
  have hsub : lateSet t D (E ++ F) ⊆ Finset.univ.filter (fun j => ¬ (x j = true)) := by
    intro j hj
    rw [lm_mem_lateSet] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hxj
    have := hEok j ((hEmem j).2 hxj)
    linarith [hj.2]
  have h2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => x j = true) p
  have h1 : knapValue p x = ∑ j ∈ Finset.univ.filter (fun j => x j = true), p j := by
    unfold knapValue; exact lm_sum_bool_real _ _ _
  unfold weightedTardy
  calc ∑ j ∈ lateSet t D (E ++ F), p j ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ (x j = true)), p j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hp i)
    _ = (∑ j, p j) - knapValue p x := by rw [h1]; linarith

theorem lm_goal {n : ℕ} (hn : 0 < n) (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hd : Monotone d) :
    ∃ V : ℝ, eq3 a' d p n (d ⟨n - 1, by omega⟩ : ℤ) = (V : WithBot ℝ) ∧
      IsLeast {w : ℝ | ∃ l : List (Fin n), IsSchedule Finset.univ l ∧ w = weightedTardy a' d p l}
        ((∑ j, p j) - V) := by
  obtain ⟨V, hV, hG⟩ := LawlerMoore.WeightedTardy.eq3_value a' d p n le_rfl (d ⟨n - 1, by omega⟩)
  refine ⟨V, hV, ?_⟩
  have hB : ∀ x : Fin n → Bool, PrefixFeasible a' d x → knapValue p x ≤ V := by
    intro x hx
    apply hG.2
    refine ⟨x, fun i hi => absurd i.isLt (by omega), fun k _ => hx k, ?_, rfl⟩
    rw [lm_T a' x (n - 1) ⟨n - 1, by omega⟩ rfl (fun i hi => absurd i.isLt (by omega))]
    exact hx _
  obtain ⟨x0, _, hx0, _, hx0v⟩ := hG.1
  have hx0' : PrefixFeasible a' d x0 := fun k => hx0 k k.isLt
  have hlow : ∀ l : List (Fin n), IsSchedule Finset.univ l →
      (∑ j, p j) - V ≤ weightedTardy a' d p l := by
    intro l hl
    obtain ⟨x, hxf, hxl⟩ := lm_part1 a' d p hd l hl
    have := hB x hxf
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl, hlw⟩ := lm_part2 a' d p hp x0 hx0'
    refine ⟨l, hl, ?_⟩
    have := hlow l hl
    rw [← hx0v] at hlw
    linarith
  · rintro w ⟨l, hl, rfl⟩
    exact hlow l hl

end

section
open LawlerMoore.WeightedTardy
open MooreLateJobs.Shared MooreLateJobs.NumLate

theorem solution {n : ℕ} (hn : 0 < n) (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hd : Monotone d) :
    ∃ V : ℝ, eq3 a' d p n (d ⟨n - 1, by omega⟩ : ℤ) = (V : WithBot ℝ) ∧
      IsLeast {w : ℝ | ∃ l : List (Fin n), IsSchedule Finset.univ l ∧ w = weightedTardy a' d p l}
        ((∑ j, p j) - V) := by
  exact lm_goal hn a' d p hp hd

end
