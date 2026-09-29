-- Prove2me | solution 1 for MooreLateJobs.NumLate.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:41:57.912276+00:00
-- url     : https://prove2.me/submissions/fbbb7a70-eeab-47d4-b267-7f563d559595

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_MooreStep
import Definitions.Def_MooreLateJobs_NumLate_earlyPart



namespace MooreLateJobs.NumLate

open Shared

section base
variable {ι : Type*} [DecidableEq ι]

theorem ml_ct_def (t : ι → ℝ) (l : List ι) (j : ι) :
    completionTime t l j = ((l.take (l.idxOf j + 1)).map t).sum := rfl

theorem ml_ct_append_left (t : ι → ℝ) (A B : List ι) (j : ι) (hj : j ∈ A) :
    completionTime t (A ++ B) j = completionTime t A j := by
  simp only [ml_ct_def, List.idxOf_append_of_mem hj]
  rw [List.take_append_of_le_length]
  have := List.idxOf_lt_length_of_mem hj
  omega

theorem ml_ct_append_right (t : ι → ℝ) (A B : List ι) (j : ι) (hj : j ∉ A) :
    completionTime t (A ++ B) j = (A.map t).sum + completionTime t B j := by
  simp only [ml_ct_def, List.idxOf_append_of_notMem hj]
  rw [List.take_append, List.take_of_length_le (by omega)]
  simp only [List.map_append, List.sum_append]
  congr 4
  omega

theorem ml_take_filter_idx (p : ι → Bool) (l : List ι) (j : ι) (hp : p j) :
    (l.filter p).take ((l.filter p).idxOf j + 1) = (l.take (l.idxOf j + 1)).filter p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases haj : a = j
    · subst haj; simp [List.filter_cons, hp]
    · by_cases hpa : p a
      · simp only [List.filter_cons, hpa, if_true, List.idxOf_cons_ne _ haj, Nat.succ_eq_add_one,
          List.take_succ_cons, ih]
      · simp only [List.filter_cons, hpa, List.idxOf_cons_ne _ haj, Nat.succ_eq_add_one,
          List.take_succ_cons]
        simp [hpa, ih]

theorem ml_ct_filter_le (t : ι → ℝ) (l : List ι) (ht : ∀ i ∈ l, 0 ≤ t i) (p : ι → Bool) (j : ι)
    (hp : p j) : completionTime t (l.filter p) j ≤ completionTime t l j := by
  rw [ml_ct_def, ml_ct_def, ml_take_filter_idx p l j hp]
  apply List.Sublist.sum_le_sum ((List.filter_sublist).map t)
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  exact ht b (List.mem_of_mem_take hb)

theorem ml_mem_lateSet (t D : ι → ℝ) (l : List ι) (j : ι) :
    j ∈ lateSet t D l ↔ j ∈ l ∧ D j < completionTime t l j := by
  simp [lateSet]

theorem ml_lateSet_sub (t D : ι → ℝ) (l : List ι) : lateSet t D l ⊆ l.toFinset :=
  Finset.filter_subset _ _

theorem ml_lateSet_filter (t D : ι → ℝ) (l : List ι) (ht : ∀ i ∈ l, 0 ≤ t i) (p : ι → Bool) :
    lateSet t D (l.filter p) ⊆ lateSet t D l := by
  intro j hj
  rw [ml_mem_lateSet] at hj ⊢
  have hmem := List.mem_filter.1 hj.1
  exact ⟨hmem.1, lt_of_lt_of_le hj.2 (ml_ct_filter_le t l ht p j hmem.2)⟩

theorem ml_ct_eq_sum (t : ι → ℝ) (l : List ι) (hl : l.Nodup) (j : ι) :
    completionTime t l j = ∑ i ∈ (l.take (l.idxOf j + 1)).toFinset, t i := by
  rw [ml_ct_def, List.sum_toFinset _ (hl.sublist (List.take_sublist _ _))]

noncomputable def mlDem (t D : ι → ℝ) (F : Finset ι) (d : ℝ) : ℝ :=
  ∑ i ∈ F.filter (fun i => D i ≤ d), t i

def MlFeas (t D : ι → ℝ) (F : Finset ι) : Prop := ∀ i ∈ F, mlDem t D F (D i) ≤ D i

theorem ml_feas_thr (t D : ι → ℝ) (F : Finset ι) (hF : MlFeas t D F) (d : ℝ)
    (hd : ∃ i ∈ F, D i ≤ d) : mlDem t D F d ≤ d := by
  obtain ⟨i0, hi0, hi0d⟩ := hd
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (F.filter (fun i => D i ≤ d)) D
    ⟨i0, Finset.mem_filter.2 ⟨hi0, hi0d⟩⟩
  have hm' := Finset.mem_filter.1 hm
  have heq : F.filter (fun i => D i ≤ d) = F.filter (fun i => D i ≤ D m) := by
    ext f
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hf, hfd⟩; exact ⟨hf, hmax f (Finset.mem_filter.2 ⟨hf, hfd⟩)⟩
    · rintro ⟨hf, hfd⟩; exact ⟨hf, le_trans hfd hm'.2⟩
  have := hF m hm'.1
  unfold mlDem at this ⊢
  rw [heq]
  linarith [hm'.2]

theorem ml_dem_mono (t D : ι → ℝ) (G F : Finset ι) (hGF : G ⊆ F) (ht : ∀ i ∈ F, 0 ≤ t i) (d : ℝ) :
    mlDem t D G d ≤ mlDem t D F d := by
  unfold mlDem
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hGF)
  intro i hi _
  exact ht i (Finset.mem_filter.1 hi).1

theorem ml_feas_mono (t D : ι → ℝ) (G F : Finset ι) (hGF : G ⊆ F) (ht : ∀ i ∈ F, 0 ≤ t i)
    (hF : MlFeas t D F) : MlFeas t D G := by
  intro i hi
  exact le_trans (ml_dem_mono t D G F hGF ht _) (ml_feas_thr t D F hF _ ⟨i, hGF hi, le_rfl⟩)

theorem ml_mem_take_idx_le (D : ι → ℝ) (S : List ι) (hS : S.Pairwise (fun a b => D a ≤ D b))
    (j : ι) (hj : j ∈ S) (i : ι) (hi : i ∈ S.take (S.idxOf j + 1)) : D i ≤ D j := by
  obtain ⟨m, hm, rfl⟩ := List.mem_take_iff_getElem.1 hi
  have hjl := List.idxOf_lt_length_of_mem hj
  rcases Nat.lt_or_ge m (S.idxOf j) with h | h
  · have := List.pairwise_iff_getElem.1 hS m (S.idxOf j) (by omega) hjl h
    rw [List.getElem_idxOf hjl] at this
    exact this
  · have : m = S.idxOf j := by omega
    subst this
    rw [List.getElem_idxOf hjl]

theorem ml_early_of_feas (t D : ι → ℝ) (S : List ι) (hnd : S.Nodup)
    (hS : S.Pairwise (fun a b => D a ≤ D b)) (ht : ∀ i ∈ S, 0 ≤ t i)
    (hF : MlFeas t D S.toFinset) : lateSet t D S = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro j hj
  rw [ml_mem_lateSet] at hj
  obtain ⟨hjS, hlt⟩ := hj
  have h1 : completionTime t S j ≤ mlDem t D S.toFinset (D j) := by
    rw [ml_ct_eq_sum t S hnd]
    unfold mlDem
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      rw [List.mem_toFinset] at hi
      exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 (List.mem_of_mem_take hi),
        ml_mem_take_idx_le D S hS j hjS i hi⟩
    · intro i hi _
      exact ht i (List.mem_toFinset.1 (Finset.mem_filter.1 hi).1)
  have h2 := hF j (List.mem_toFinset.2 hjS)
  linarith

theorem ml_feas_of_sched (t D : ι → ℝ) (S : List ι) (hnd : S.Nodup) (ht : ∀ i ∈ S, 0 ≤ t i)
    (hS : lateSet t D S = ∅) : MlFeas t D S.toFinset := by
  intro i hi
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (S.toFinset.filter (fun x => D x ≤ D i))
    (fun x => S.idxOf x) ⟨i, Finset.mem_filter.2 ⟨hi, le_rfl⟩⟩
  have hm' := Finset.mem_filter.1 hm
  have hmS : m ∈ S := List.mem_toFinset.1 hm'.1
  have hsub : S.toFinset.filter (fun x => D x ≤ D i) ⊆ (S.take (S.idxOf m + 1)).toFinset := by
    intro x hx
    have hxS : x ∈ S := List.mem_toFinset.1 (Finset.mem_filter.1 hx).1
    have hle := hmax x hx
    have hxl := List.idxOf_lt_length_of_mem hxS
    rw [List.mem_toFinset, List.mem_take_iff_getElem]
    exact ⟨S.idxOf x, by omega, List.getElem_idxOf hxl⟩
  have h1 : mlDem t D S.toFinset (D i) ≤ completionTime t S m := by
    rw [ml_ct_eq_sum t S hnd]
    unfold mlDem
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro x hx _
    exact ht x (List.mem_of_mem_take (List.mem_toFinset.1 hx))
  have h2 : completionTime t S m ≤ D m := by
    by_contra h
    have : m ∈ lateSet t D S := (ml_mem_lateSet t D S m).2 ⟨hmS, lt_of_not_ge h⟩
    rw [hS] at this
    simp at this
  linarith [hm'.2]

theorem ml_toFinset_of_sched (J : Finset ι) (l : List ι) (h : IsSchedule J l) : l.toFinset = J := by
  ext x; simp [h.2 x]

theorem ml_edd_exists (D : ι → ℝ) (F : Finset ι) :
    ∃ S : List ι, IsSchedule F S ∧ S.Pairwise (fun a b => D a ≤ D b) := by
  refine ⟨F.toList.mergeSort (fun a b => decide (D a ≤ D b)), ⟨?_, ?_⟩, ?_⟩
  · exact (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList F)
  · intro x
    rw [(List.mergeSort_perm _ _).mem_iff]
    simp
  · have := List.pairwise_mergeSort (le := fun a b => decide (D a ≤ D b))
      (by intro a b c h1 h2; simp at *; linarith)
      (by intro a b; simp; exact le_total _ _) F.toList
    simpa using this

theorem jackson_core (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) :
    (∃ S : List ι, Shared.IsSchedule J S ∧ lateSet t D S = ∅) ↔
      ∀ S : List ι, Shared.IsSchedule J S → S.Pairwise (fun a b => D a ≤ D b) →
        lateSet t D S = ∅ := by
  constructor
  · rintro ⟨S0, hS0, hl0⟩ S hS hdd
    have hF := ml_feas_of_sched t D S0 hS0.1 (fun i hi => ht i ((hS0.2 i).1 hi)) hl0
    rw [ml_toFinset_of_sched J S0 hS0] at hF
    apply ml_early_of_feas t D S hS.1 hdd (fun i hi => ht i ((hS.2 i).1 hi))
    rwa [ml_toFinset_of_sched J S hS]
  · intro h
    obtain ⟨S, hS, hdd⟩ := ml_edd_exists D J
    exact ⟨S, hS, h S hS hdd⟩


theorem ml_mem_earlyPart (t D : ι → ℝ) (S : List ι) (j : ι) :
    j ∈ earlyPart t D S ↔ j ∈ S ∧ j ∉ lateSet t D S := by
  simp [earlyPart]

theorem ml_mem_latePart (t D : ι → ℝ) (S : List ι) (j : ι) :
    j ∈ latePart t D S ↔ j ∈ lateSet t D S := by
  simp only [latePart, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨List.mem_toFinset.1 (ml_lateSet_sub t D S h), h⟩

theorem ml_not_late (t D : ι → ℝ) (S : List ι) (j : ι) (hj : j ∈ S) (h : j ∉ lateSet t D S) :
    completionTime t S j ≤ D j := by
  by_contra h'
  exact h ((ml_mem_lateSet t D S j).2 ⟨hj, lt_of_not_ge h'⟩)

theorem ml_early_ct_le (t D : ι → ℝ) (S : List ι) (ht : ∀ i ∈ S, 0 ≤ t i) (j : ι)
    (hj : j ∈ earlyPart t D S) : completionTime t (earlyPart t D S) j ≤ D j := by
  have h := (ml_mem_earlyPart t D S j).1 hj
  have h1 := ml_ct_filter_le t S ht (fun j => decide (j ∉ lateSet t D S)) j (by simpa using h.2)
  exact le_trans h1 (ml_not_late t D S j h.1 h.2)

theorem lemma1_core (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i)
    (S : List ι) (hS : IsOptimal t D J S) :
    (lateSet t D (earlyPart t D S ++ latePart t D S)).card = (lateSet t D S).card ∧
    ∀ P : List ι, P.Perm (latePart t D S) →
      (lateSet t D (earlyPart t D S ++ P)).card = (lateSet t D S).card := by
  have htS : ∀ i ∈ S, 0 ≤ t i := fun i hi => ht i ((hS.1.2 i).1 hi)
  have key : ∀ P : List ι, P.Perm (latePart t D S) →
      (lateSet t D (earlyPart t D S ++ P)).card = (lateSet t D S).card := by
    intro P hP
    have hsub : lateSet t D (earlyPart t D S ++ P) ⊆ lateSet t D S := by
      intro j hj
      rw [ml_mem_lateSet] at hj
      obtain ⟨hjm, hlt⟩ := hj
      by_cases hjE : j ∈ earlyPart t D S
      · rw [ml_ct_append_left t _ _ j hjE] at hlt
        exact absurd (ml_early_ct_le t D S htS j hjE) (not_le.2 hlt)
      · have : j ∈ P := by
          rcases List.mem_append.1 hjm with h | h
          · exact absurd h hjE
          · exact h
        exact (ml_mem_latePart t D S j).1 (hP.mem_iff.1 this)
    have hsch : IsSchedule J (earlyPart t D S ++ P) := by
      refine ⟨?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hS.1.1.filter _, (hP.nodup_iff).2 (hS.1.1.filter _), ?_⟩
        intro a ha b hb hab
        subst hab
        exact ((ml_mem_earlyPart t D S a).1 ha).2 ((ml_mem_latePart t D S a).1 (hP.mem_iff.1 hb))
      · intro x
        rw [← hS.1.2 x, List.mem_append, hP.mem_iff, ml_mem_earlyPart, ml_mem_latePart]
        constructor
        · rintro (h | h)
          · exact h.1
          · exact List.mem_toFinset.1 (ml_lateSet_sub t D S h)
        · intro h
          by_cases hl : x ∈ lateSet t D S
          · exact Or.inr hl
          · exact Or.inl ⟨h, hl⟩
    exact le_antisymm (Finset.card_le_card hsub) (hS.2 _ hsch)
  exact ⟨key _ (List.Perm.refl _), key⟩

end base
end MooreLateJobs.NumLate

open MooreLateJobs.NumLate
open MooreLateJobs

theorem solution {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (S : List ι) (hS : IsOptimal t D J S) :
    (lateSet t D (earlyPart t D S ++ latePart t D S)).card = (lateSet t D S).card ∧
    ∀ P : List ι, P.Perm (latePart t D S) →
      (lateSet t D (earlyPart t D S ++ P)).card = (lateSet t D S).card := by
  exact lemma1_core J t D ht S hS
