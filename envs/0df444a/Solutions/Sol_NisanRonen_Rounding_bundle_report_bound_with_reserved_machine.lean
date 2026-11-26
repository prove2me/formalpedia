-- Prove2me | solution 1 for NisanRonen.Rounding.bundle_report_bound_with_reserved_machine
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:38:16.495828+00:00
-- url     : https://prove2.me/submissions/934806ee-a28d-4e09-83e0-d4f822084668

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

open NisanRonen.Rounding
open scoped BigOperators

set_option autoImplicit false

private theorem rounded_entry_nonneg {δ a z : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hz : a ≤ z) :
    0 ≤ roundUp δ z := by
  unfold roundUp
  exact mul_nonneg hδ.le (by exact_mod_cast Int.ceil_nonneg (div_nonneg (ha.le.trans hz) hδ.le))

private theorem mem_load_set {n k : ℕ} (x : Fin k → Fin n) (j : Fin k) (l : Fin n) :
    j ∈ Finset.univ.filter (fun h => x h = l) ↔ x j = l := by simp

private theorem rounded_task_le_span {n k : ℕ} [NeZero n] {δ : ℝ}
    (x : Fin k → Fin n) (u : Fin n → Fin k → ℝ)
    (hu : ∀ j, 0 ≤ roundUp δ (u (x j) j)) (j : Fin k) :
    roundUp δ (u (x j) j) ≤ roundedMakespan δ x (corrStar x u) := by
  unfold roundedMakespan makespan
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (x j)))
  exact Finset.single_le_sum (f := fun l => roundUp δ (u (x l) l))
    (fun l _ => hu l) ((mem_load_set x j (x j)).2 rfl)

theorem solution {n k : ℕ} [NeZero n] {a b δ m : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hma : a ≤ m) (hmb : m ≤ b) (hmround : roundUp δ m = m)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (i spare : Fin n) (hspare : spare ≠ i)
    (t r : Fin k → ℝ) (ht : ∀ j, a ≤ t j ∧ t j ≤ b) (hr : ∀ j, a ≤ r j ∧ r j ≤ b)
    (hop : DeclarationOptimal f δ a b i t r)
    (S : Finset (Fin k)) (j₀ : Fin k) (hj₀ : j₀ ∈ S)
    (bg : Fin k → Fin n) (hbg : ∀ j (_ : j ∉ S), bg j ≠ i ∧ bg j ≠ spare)
    (hbgload : ∀ l : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j => j ∉ S ∧ bg j = l), roundUp δ a) < m)
    (htload : (∑ j ∈ S, roundUp δ (t j)) < m)
    (hrErase : (∑ j ∈ S.erase j₀, roundUp δ (r j)) ≤ m) :
    (∑ j ∈ S, roundUp δ (r j)) ≤ m := by
  classical
  have hab : a ≤ b := hma.trans hmb
  let v : Fin n → Fin k → ℝ :=
    fun l j => if l = i then r j else if j ∈ S then m else a
  have hv (l : Fin n) (j : Fin k) : a ≤ v l j ∧ v l j ≤ b := by
    by_cases hl : l = i <;> by_cases hj : j ∈ S <;>
      simp [v, hl, hj, hr, hma, hmb, hab]
  have hvi : v i = r := by funext j; simp [v]
  let fallback : Fin k → Fin n :=
    fun j => if j ∈ S then (if j = j₀ then spare else i) else bg j
  have fallback_i (j : Fin k) : fallback j = i ↔ j ∈ S ∧ j ≠ j₀ := by
    by_cases hs : j ∈ S
    · by_cases hj : j = j₀ <;> simp [fallback, hs, hj, hj₀, hspare]
    · simp [fallback, hs, (hbg j hs).1]
  have fallback_spare (j : Fin k) : fallback j = spare ↔ j = j₀ := by
    by_cases hj : j = j₀
    · subst j; simp [fallback, hj₀]
    · by_cases hs : j ∈ S
      · simp [fallback, hs, hj, Ne.symm hspare]
      · simp [fallback, hs, hj, (hbg j hs).2]
  have fallback_other (l : Fin n) (hli : l ≠ i) (hls : l ≠ spare) (j : Fin k) :
      fallback j = l ↔ j ∉ S ∧ bg j = l := by
    by_cases hs : j ∈ S
    · by_cases hj : j = j₀ <;> simp [fallback, hs, hj, hj₀, Ne.symm hli, Ne.symm hls]
    · simp [fallback, hs]
  have hfall : roundedMakespan δ fallback (corrStar fallback v) ≤ m := by
    unfold roundedMakespan makespan
    apply Finset.sup'_le
    intro l _
    have hval : load fallback (fun j => roundUp δ (corrStar fallback v j)) l =
        ∑ j ∈ Finset.univ.filter (fun j => fallback j = l), roundUp δ (v l j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [corrStar, (mem_load_set fallback j l).1 hj]
    rw [hval]
    by_cases hli : l = i
    · subst l
      have hset : Finset.univ.filter (fun j => fallback j = i) = S.erase j₀ := by
        ext j
        simp [fallback_i, Finset.mem_erase, and_comm]
      simpa [hset, v] using hrErase
    · by_cases hls : l = spare
      · subst l
        have hset : Finset.univ.filter (fun j => fallback j = spare) = {j₀} := by
          ext j
          simp [fallback_spare]
        simp [hset, v, hspare, hj₀, hmround]
      · have hset : Finset.univ.filter (fun j => fallback j = l) =
            Finset.univ.filter (fun j => j ∉ S ∧ bg j = l) := by
          ext j
          simp [fallback_other l hli hls]
        rw [hset]
        refine le_trans ?_ (hbgload l).le
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro j hj
        simp [v, hli, (Finset.mem_filter.1 hj).2.1]
  let x := allocOf f δ v
  have hx : roundedMakespan δ x (corrStar x v) ≤ m := ((hf k v hv).2 fallback).trans hfall
  by_contra hbad
  have hsome : ∃ j ∈ S, x j ≠ i := by
    by_contra hnone
    push Not at hnone
    have hsub : S ⊆ Finset.univ.filter (fun j => x j = i) :=
      fun j hj => (mem_load_set x j i).2 (hnone j hj)
    have hrewrite : (∑ j ∈ S, roundUp δ (corrStar x v j)) =
        ∑ j ∈ S, roundUp δ (r j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [corrStar, v, hnone j hj]
    apply hbad
    rw [← hrewrite]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => ?_)) ?_
    · exact rounded_entry_nonneg ha hδ (hv (x j) j).1
    · exact (Finset.le_sup' _ (Finset.mem_univ i)).trans hx
  obtain ⟨badJob, hbS, hbx⟩ := hsome
  let v' := Function.update v i t
  have hv' (l : Fin n) (j : Fin k) : a ≤ v' l j ∧ v' l j ≤ b := by
    by_cases hl : l = i
    · subst l; simpa [v'] using ht j
    · simpa [v', Function.update_of_ne hl] using hv l j
  have hxlo := rounded_task_le_span x v'
    (fun j => rounded_entry_nonneg ha hδ (hv' (x j) j).1) badJob
  have hxjob : v' (x badJob) badJob = m := by
    simp [v', v, hbx, hbS]
  rw [hxjob, hmround] at hxlo
  let cmp : Fin k → Fin n := fun j => if j ∈ S then i else bg j
  have hcmp : roundedMakespan δ cmp (corrStar cmp v') < m := by
    unfold roundedMakespan makespan
    apply (Finset.sup'_lt_iff _).2
    intro l _
    have hval : load cmp (fun j => roundUp δ (corrStar cmp v' j)) l =
        ∑ j ∈ Finset.univ.filter (fun j => cmp j = l), roundUp δ (v' l j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [corrStar, (mem_load_set cmp j l).1 hj]
    rw [hval]
    by_cases hli : l = i
    · subst l
      have hset : Finset.univ.filter (fun j => cmp j = i) = S := by
        ext j
        by_cases hj : j ∈ S <;> simp [cmp, hj, hbg]
      simpa [hset, v'] using htload
    · have hset : Finset.univ.filter (fun j => cmp j = l) =
            Finset.univ.filter (fun j => j ∉ S ∧ bg j = l) := by
          ext j
          by_cases hj : j ∈ S <;> simp [cmp, hj, Ne.symm hli]
      rw [hset]
      have he : (∑ j ∈ Finset.univ.filter (fun j => j ∉ S ∧ bg j = l), roundUp δ (v' l j)) =
          ∑ j ∈ Finset.univ.filter (fun j => j ∉ S ∧ bg j = l), roundUp δ a := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [v', v, hli, (Finset.mem_filter.1 hj).2.1]
      rw [he]
      exact hbgload l
  have hc := hop v hv hvi cmp
  exact (lt_of_le_of_lt (hxlo.trans hc) hcmp).false
