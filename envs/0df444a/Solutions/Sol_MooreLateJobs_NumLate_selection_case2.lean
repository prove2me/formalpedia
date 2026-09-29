-- Prove2me | solution 1 for MooreLateJobs.NumLate.selection_case2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:48:10.325665+00:00
-- url     : https://prove2.me/submissions/756508dc-d03c-4cd8-81a8-82fea7e6752c

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


theorem ml_sched_perm (J : Finset ι) (l l' : List ι) (h : IsSchedule J l) (hp : l'.Perm l) :
    IsSchedule J l' := ⟨hp.nodup_iff.2 h.1, fun x => by rw [hp.mem_iff]; exact h.2 x⟩

theorem ml_edd_early (t D : ι → ℝ) (A AD : List ι) (hA : A.Nodup) (htA : ∀ i ∈ A, 0 ≤ t i)
    (hAe : lateSet t D A = ∅) (hAD : AD.Perm A) (hdd : AD.Pairwise (fun a b => D a ≤ D b)) :
    lateSet t D AD = ∅ := by
  have hF := ml_feas_of_sched t D A hA htA hAe
  apply ml_early_of_feas t D AD (hAD.nodup_iff.2 hA) hdd (fun i hi => htA i (hAD.mem_iff.1 hi))
  rwa [List.toFinset_eq_of_perm _ _ hAD]

theorem lemma2_core (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i)
    (S : List ι) (hS : IsOptimal t D J S) (hform : S = earlyPart t D S ++ latePart t D S)
    (AD : List ι) (hAD : AD.Perm (earlyPart t D S)) (hdd : AD.Pairwise (fun a b => D a ≤ D b)) :
    IsOptimal t D J (AD ++ latePart t D S) ∧
      lateSet t D (AD ++ latePart t D S) = lateSet t D S := by
  have htS : ∀ i ∈ S, 0 ≤ t i := fun i hi => ht i ((hS.1.2 i).1 hi)
  have hEnd : (earlyPart t D S).Nodup := hS.1.1.filter _
  have hEt : ∀ i ∈ earlyPart t D S, 0 ≤ t i := fun i hi => htS i ((ml_mem_earlyPart t D S i).1 hi).1
  have hEe : lateSet t D (earlyPart t D S) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro j hj
    rw [ml_mem_lateSet] at hj
    exact absurd (ml_early_ct_le t D S htS j hj.1) (not_le.2 hj.2)
  have hADe := ml_edd_early t D _ AD hEnd hEt hEe hAD hdd
  have hsum : (AD.map t).sum = ((earlyPart t D S).map t).sum := (hAD.map t).sum_eq
  have hlate : lateSet t D (AD ++ latePart t D S) = lateSet t D S := by
    ext j
    rw [ml_mem_lateSet, ml_mem_lateSet]
    by_cases hjE : j ∈ earlyPart t D S
    · have hjAD : j ∈ AD := hAD.mem_iff.2 hjE
      rw [ml_ct_append_left t _ _ j hjAD]
      constructor
      · rintro ⟨_, h⟩
        have : j ∈ lateSet t D AD := (ml_mem_lateSet t D AD j).2 ⟨hjAD, h⟩
        rw [hADe] at this; simp at this
      · rintro ⟨h1, h2⟩
        exact absurd ((ml_mem_lateSet t D S j).2 ⟨h1, h2⟩) ((ml_mem_earlyPart t D S j).1 hjE).2
    · have hjAD : j ∉ AD := fun h => hjE (hAD.mem_iff.1 h)
      have hctS : completionTime t S j =
          completionTime t (earlyPart t D S ++ latePart t D S) j := by rw [← hform]
      rw [ml_ct_append_right t _ _ j hjAD, hsum, hctS, ml_ct_append_right t _ _ j hjE]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases List.mem_append.1 h1 with h | h
        · exact absurd h hjAD
        · exact List.mem_toFinset.1 (ml_lateSet_sub t D S ((ml_mem_latePart t D S j).1 h))
      · rintro ⟨h1, h2⟩
        refine ⟨List.mem_append.2 (Or.inr ?_), h2⟩
        rw [ml_mem_latePart, ml_mem_lateSet]
        refine ⟨h1, ?_⟩
        rw [hctS, ml_ct_append_right t _ _ j hjE]; exact h2
  have hperm : (AD ++ latePart t D S).Perm S := by
    have h1 : (AD ++ latePart t D S).Perm (earlyPart t D S ++ latePart t D S) :=
      hAD.append_right _
    have h2 : (earlyPart t D S ++ latePart t D S).Perm S := by rw [← hform]
    exact h1.trans h2
  refine ⟨⟨ml_sched_perm J S _ hS.1 hperm, ?_⟩, hlate⟩
  intro l' hl'
  rw [hlate]; exact hS.2 l' hl'

theorem lemma3_core (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i)
    (S : List ι) (hS : IsOptimal t D J S)
    (Jstar : Finset ι) (hJstar : Jstar ⊆ lateSet t D S)
    (S' : List ι) (hS' : IsOptimal t D (J \ Jstar) S')
    (hform : S' = earlyPart t D S' ++ latePart t D S')
    (P'' : List ι) (hP'' : Shared.IsSchedule (Jstar ∪ lateSet t D S') P'') :
    IsOptimal t D J (earlyPart t D S' ++ P'') ∧
      lateSet t D (earlyPart t D S' ++ P'') = Jstar ∪ lateSet t D S' := by
  have htS : ∀ i ∈ S, 0 ≤ t i := fun i hi => ht i ((hS.1.2 i).1 hi)
  have hS'J : ∀ x ∈ S', x ∈ J ∧ x ∉ Jstar := fun x hx => by
    have := (hS'.1.2 x).1 hx; simpa using this
  have htS' : ∀ i ∈ S', 0 ≤ t i := fun i hi => ht i (hS'J i hi).1
  have hJstarJ : ∀ x ∈ Jstar, x ∈ J := fun x hx =>
    (hS.1.2 x).1 (List.mem_toFinset.1 (ml_lateSet_sub t D S (hJstar hx)))
  -- (a)
  have hsub : lateSet t D (earlyPart t D S' ++ P'') ⊆ Jstar ∪ lateSet t D S' := by
    intro j hj
    rw [ml_mem_lateSet] at hj
    obtain ⟨hjm, hlt⟩ := hj
    by_cases hjE : j ∈ earlyPart t D S'
    · rw [ml_ct_append_left t _ _ j hjE] at hlt
      exact absurd (ml_early_ct_le t D S' htS' j hjE) (not_le.2 hlt)
    · rcases List.mem_append.1 hjm with h | h
      · exact absurd h hjE
      · exact (hP''.2 j).1 h
  -- (b)
  have hb : (lateSet t D S').card + Jstar.card ≤ (lateSet t D S).card := by
    have hsch : IsSchedule (J \ Jstar) (S.filter (fun x => decide (x ∉ Jstar))) := by
      refine ⟨hS.1.1.filter _, fun x => ?_⟩
      simp [hS.1.2 x]
    have h1 := hS'.2 _ hsch
    have h2 : lateSet t D (S.filter (fun x => decide (x ∉ Jstar))) ⊆ lateSet t D S \ Jstar := by
      intro j hj
      rw [Finset.mem_sdiff]
      refine ⟨ml_lateSet_filter t D S htS _ hj, ?_⟩
      have := List.mem_toFinset.1 (ml_lateSet_sub t D _ hj)
      simpa using (List.mem_filter.1 this).2
    have h3 := Finset.card_le_card h2
    have h4 := Finset.card_sdiff_add_card_eq_card hJstar
    omega
  have hdisj : Disjoint Jstar (lateSet t D S') := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (hS'J x (List.mem_toFinset.1 (ml_lateSet_sub t D S' hx'))).2 hx
  have hcardU := Finset.card_union_of_disjoint hdisj
  -- (c)
  have hsch : IsSchedule J (earlyPart t D S' ++ P'') := by
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hS'.1.1.filter _, hP''.1, ?_⟩
      intro a ha b hb hab
      subst hab
      have ha' := (ml_mem_earlyPart t D S' a).1 ha
      rcases Finset.mem_union.1 ((hP''.2 a).1 hb) with h | h
      · exact (hS'J a ha'.1).2 h
      · exact ha'.2 h
    · intro x
      rw [List.mem_append, hP''.2 x, ml_mem_earlyPart, Finset.mem_union]
      constructor
      · rintro (h | h | h)
        · exact (hS'J x h.1).1
        · exact hJstarJ x h
        · exact (hS'J x (List.mem_toFinset.1 (ml_lateSet_sub t D S' h))).1
      · intro hx
        by_cases hxs : x ∈ Jstar
        · exact Or.inr (Or.inl hxs)
        · have hxS' : x ∈ S' := (hS'.1.2 x).2 (by simp [hx, hxs])
          by_cases hl : x ∈ lateSet t D S'
          · exact Or.inr (Or.inr hl)
          · exact Or.inl ⟨hxS', hl⟩
  -- (d)
  have hopt := hS.2 _ hsch
  have heq : lateSet t D (earlyPart t D S' ++ P'') = Jstar ∪ lateSet t D S' := by
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  refine ⟨⟨hsch, ?_⟩, heq⟩
  intro l' hl'
  have := hS.2 l' hl'
  rw [heq]; omega


theorem ml_take_succ_toFinset (rej : List ι) (k : ℕ) (hk : k < rej.length) :
    (rej.take (k + 1)).toFinset = insert rej[k] (rej.take k).toFinset := by
  ext x
  rw [List.mem_toFinset, List.take_add_one, List.getElem?_eq_getElem hk, Finset.mem_insert,
    List.mem_toFinset, List.mem_append]
  simp only [Option.toList_some, List.mem_singleton]
  tauto

theorem repeated_elimination_core (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i)
    (rej : List ι) (hnd : rej.Nodup) (hsub : ∀ j ∈ rej, j ∈ J)
    (hfound : ∀ (k : ℕ) (hk : k < rej.length), ∃ S : List ι,
      IsOptimal t D (J \ (rej.take k).toFinset) S ∧ rej[k] ∈ lateSet t D S)
    (hfeas : ∃ S : List ι, Shared.IsSchedule (J \ rej.toFinset) S ∧ lateSet t D S = ∅)
    (AD : List ι) (hAD : Shared.IsSchedule (J \ rej.toFinset) AD)
    (hdd : AD.Pairwise (fun a b => D a ≤ D b))
    (P : List ι) (hP : P.Perm rej) :
    IsOptimal t D J (AD ++ P) := by
  have hC : ∀ n k, k + n = rej.length → ∀ l', IsSchedule (J \ (rej.take k).toFinset) l' →
      rej.length - k ≤ (lateSet t D l').card := by
    intro n
    induction n with
    | zero => intro k hk l' _; omega
    | succ n ih =>
      intro k hk l' hl'
      have hkl : k < rej.length := by omega
      obtain ⟨S, hS, hq⟩ := hfound k hkl
      have h1 := hS.2 l' hl'
      have htS : ∀ i ∈ S, 0 ≤ t i := fun i hi => by
        have := (hS.1.2 i).1 hi; exact ht i (Finset.mem_sdiff.1 this).1
      have hsch : IsSchedule (J \ (rej.take (k + 1)).toFinset)
          (S.filter (fun x => decide (x ≠ rej[k]))) := by
        refine ⟨hS.1.1.filter _, fun x => ?_⟩
        rw [ml_take_succ_toFinset rej k hkl, List.mem_filter, hS.1.2 x]
        simp only [Finset.mem_sdiff, Finset.mem_insert, decide_eq_true_eq]
        tauto
      have h2 := ih (k + 1) (by omega) _ hsch
      have h3 : lateSet t D (S.filter (fun x => decide (x ≠ rej[k]))) ⊆ (lateSet t D S).erase rej[k] := by
        intro j hj
        rw [Finset.mem_erase]
        refine ⟨?_, ml_lateSet_filter t D S htS _ hj⟩
        have := List.mem_toFinset.1 (ml_lateSet_sub t D _ hj)
        simpa using (List.mem_filter.1 this).2
      have h4 := Finset.card_le_card h3
      rw [Finset.card_erase_of_mem hq] at h4
      have h5 : 0 < (lateSet t D S).card := Finset.card_pos.2 ⟨_, hq⟩
      omega
  have htR : ∀ i ∈ J \ rej.toFinset, 0 ≤ t i := fun i hi => ht i (Finset.mem_sdiff.1 hi).1
  have hADe : lateSet t D AD = ∅ := (jackson_core _ t D htR).1 hfeas AD hAD hdd
  have hPnd : P.Nodup := hP.nodup_iff.2 hnd
  have hsch : IsSchedule J (AD ++ P) := by
    refine ⟨?_, fun x => ?_⟩
    · rw [List.nodup_append]
      refine ⟨hAD.1, hPnd, ?_⟩
      intro a ha b hb hab
      subst hab
      have := (hAD.2 a).1 ha
      simp only [Finset.mem_sdiff, List.mem_toFinset] at this
      exact this.2 (hP.mem_iff.1 hb)
    · rw [List.mem_append, hAD.2 x, hP.mem_iff]
      simp only [Finset.mem_sdiff, List.mem_toFinset]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact hsub x h
      · intro hx; by_cases h : x ∈ rej
        · exact Or.inr h
        · exact Or.inl ⟨hx, h⟩
  have hlsub : lateSet t D (AD ++ P) ⊆ P.toFinset := by
    intro j hj
    rw [ml_mem_lateSet] at hj
    obtain ⟨hjm, hlt⟩ := hj
    rcases List.mem_append.1 hjm with h | h
    · rw [ml_ct_append_left t _ _ j h] at hlt
      have : j ∈ lateSet t D AD := (ml_mem_lateSet t D AD j).2 ⟨h, hlt⟩
      rw [hADe] at this; simp at this
    · exact List.mem_toFinset.2 h
  have hcard : (lateSet t D (AD ++ P)).card ≤ rej.length := by
    have := Finset.card_le_card hlsub
    rw [List.toFinset_card_of_nodup hPnd, hP.length_eq] at this
    exact this
  refine ⟨hsch, fun l' hl' => ?_⟩
  have := hC rej.length 0 (by omega) l' (by simpa using hl')
  omega


theorem ml_dem_insert (t D : ι → ℝ) (G : Finset ι) (j : ι) (hj : j ∉ G) (d : ℝ) :
    mlDem t D (insert j G) d = (if D j ≤ d then t j else 0) + mlDem t D G d := by
  unfold mlDem
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (fun h' => hj (Finset.mem_filter.1 h').1)]
  · simp

theorem ml_exchange (Jc : Finset ι) (t D : ι → ℝ) (ht : ∀ i ∈ Jc, 0 ≤ t i)
    (pre : Finset ι) (hpreJ : pre ⊆ Jc) (hpreF : MlFeas t D pre)
    (q : ι) (htpre : ∀ a ∈ pre, t a ≤ t q) (htrest : ∀ b ∈ Jc, b ∉ pre → b ≠ q → t q ≤ t b)
    (F : Finset ι) (hFJ : F ⊆ Jc) (hF : MlFeas t D F) (j : ι) (hjpre : j ∈ pre) (hjF : j ∉ F)
    (hinf : ¬ MlFeas t D (insert j F)) :
    ∃ x ∈ F, x ∉ pre ∧ MlFeas t D (insert j (F.erase x)) := by
  have hjJ : j ∈ Jc := hpreJ hjpre
  have htI : ∀ i ∈ insert j F, 0 ≤ t i := by
    intro i hi; rcases Finset.mem_insert.1 hi with h | h
    · subst h; exact ht _ hjJ
    · exact ht i (hFJ h)
  -- violations
  classical
  have hV : ((insert j F).filter (fun i => D i < mlDem t D (insert j F) (D i))).Nonempty := by
    by_contra hne
    apply hinf
    intro i hi
    by_contra hlt
    exact hne ⟨i, Finset.mem_filter.2 ⟨hi, lt_of_not_ge hlt⟩⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ D hV
  have hi0' := Finset.mem_filter.1 hi0
  have hdemF : ∀ d, d < D j → mlDem t D (insert j F) d = mlDem t D F d := by
    intro d hd
    rw [ml_dem_insert t D F j hjF, if_neg (not_le.2 hd), zero_add]
  have hjd0 : D j ≤ D i0 := by
    by_contra h
    push_neg at h
    have hi0F : i0 ∈ F := by
      rcases Finset.mem_insert.1 hi0'.1 with h' | h'
      · subst h'; exact absurd h (lt_irrefl _)
      · exact h'
    have := hF i0 hi0F
    rw [hdemF _ h] at hi0'
    linarith [hi0'.2]
  have hx : ∃ x ∈ F, D x ≤ D i0 ∧ x ∉ pre := by
    by_contra hno
    push_neg at hno
    have hsub : (insert j F).filter (fun i => D i ≤ D i0) ⊆ pre.filter (fun i => D i ≤ D i0) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      refine ⟨?_, hy.2⟩
      rcases Finset.mem_insert.1 hy.1 with h | h
      · subst h; exact hjpre
      · exact hno y h hy.2
    have h1 : mlDem t D (insert j F) (D i0) ≤ mlDem t D pre (D i0) := by
      unfold mlDem
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i hi _
      exact ht i (hpreJ (Finset.mem_filter.1 hi).1)
    have h2 := ml_feas_thr t D pre hpreF (D i0) ⟨j, hjpre, hjd0⟩
    linarith [hi0'.2]
  obtain ⟨x, hxF, hxd, hxpre⟩ := hx
  refine ⟨x, hxF, hxpre, ?_⟩
  have htjx : t j ≤ t x := by
    by_cases hxq : x = q
    · subst hxq; exact htpre j hjpre
    · exact le_trans (htpre j hjpre) (htrest x (hFJ hxF) hxpre hxq)
  have hjE : j ∉ F.erase x := fun h => hjF (Finset.mem_of_mem_erase h)
  intro i hi
  by_cases hxi : D x ≤ D i
  · rw [ml_dem_insert t D _ j hjE]
    have hFx : mlDem t D F (D i) = t x + mlDem t D (F.erase x) (D i) := by
      conv_lhs => rw [← Finset.insert_erase hxF]
      rw [ml_dem_insert t D _ x (Finset.notMem_erase x F), if_pos hxi]
    have h3 := ml_feas_thr t D F hF (D i) ⟨x, hxF, hxi⟩
    have h4 : (if D j ≤ D i then t j else 0) ≤ t j := by
      split_ifs
      · exact le_rfl
      · exact ht j hjJ
    linarith
  · push_neg at hxi
    have hsubI : insert j (F.erase x) ⊆ insert j F :=
      Finset.insert_subset_insert _ (Finset.erase_subset _ _)
    have hnv : mlDem t D (insert j F) (D i) ≤ D i := by
      by_contra hc
      have := hmin i (Finset.mem_filter.2 ⟨hsubI hi, lt_of_not_ge hc⟩)
      linarith
    exact le_trans (ml_dem_mono t D _ _ hsubI htI _) hnv

theorem ml_early_set_feas (Jc : Finset ι) (t D : ι → ℝ) (ht : ∀ i ∈ Jc, 0 ≤ t i) (l : List ι)
    (hl : IsSchedule Jc l) : MlFeas t D (Jc \ lateSet t D l) := by
  have htl : ∀ i ∈ l, 0 ≤ t i := fun i hi => ht i ((hl.2 i).1 hi)
  have h1 : lateSet t D (l.filter (fun x => decide (x ∉ lateSet t D l))) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro j hj
    have h2 := ml_lateSet_filter t D l htl _ hj
    have h3 := List.mem_toFinset.1 (ml_lateSet_sub t D _ hj)
    simp only [List.mem_filter, decide_eq_true_eq] at h3
    exact h3.2 h2
  have := ml_feas_of_sched t D _ (hl.1.filter _) (fun i hi => htl i (List.mem_of_mem_filter hi)) h1
  have heq : (l.filter (fun x => decide (x ∉ lateSet t D l))).toFinset = Jc \ lateSet t D l := by
    ext x; simp [hl.2 x]
  rwa [heq] at this

theorem ml_card_early (Jc : Finset ι) (t D : ι → ℝ) (l : List ι) (hl : IsSchedule Jc l) :
    (Jc \ lateSet t D l).card + (lateSet t D l).card = Jc.card := by
  apply Finset.card_sdiff_add_card_eq_card
  rw [← ml_toFinset_of_sched Jc l hl]; exact ml_lateSet_sub t D l

theorem selection_core (Jc : Finset ι) (t D : ι → ℝ) (ht : ∀ i ∈ Jc, 0 ≤ t i)
    (pre : Finset ι) (hpreJ : pre ⊆ Jc) (hpreF : MlFeas t D pre)
    (q : ι) (hq : q ∈ Jc) (hqpre : q ∉ pre)
    (htpre : ∀ a ∈ pre, t a ≤ t q) (htrest : ∀ b ∈ Jc, b ∉ pre → b ≠ q → t q ≤ t b)
    (hinf : ¬ MlFeas t D (insert q pre)) :
    ∃ S : List ι, IsOptimal t D Jc S ∧ q ∈ lateSet t D S := by
  classical
  obtain ⟨F0, hF0, hmax0⟩ := Finset.exists_max_image (Jc.powerset.filter (fun G => MlFeas t D G))
    Finset.card ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, fun i hi => by simp at hi⟩⟩
  have hF0' := Finset.mem_filter.1 hF0
  set N := F0.card with hN
  have hmax : ∀ G ⊆ Jc, MlFeas t D G → G.card ≤ N := fun G hG hGf =>
    hmax0 G (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hG, hGf⟩)
  -- iteration
  have hiter : ∀ n (F : Finset ι), F ⊆ Jc → MlFeas t D F → q ∈ F → (pre \ F).card = n →
      F.card = N → ∃ G ⊆ Jc, MlFeas t D G ∧ q ∉ G ∧ G.card = N := by
    intro n
    induction n with
    | zero =>
      intro F hFJ hF hqF hc _
      exfalso
      apply hinf
      apply ml_feas_mono t D _ F _ (fun i hi => ht i (hFJ hi)) hF
      intro y hy
      rcases Finset.mem_insert.1 hy with h | h
      · subst h; exact hqF
      · by_contra hyF
        have : y ∈ pre \ F := Finset.mem_sdiff.2 ⟨h, hyF⟩
        rw [Finset.card_eq_zero] at hc
        rw [hc] at this; simp at this
    | succ m ih =>
      intro F hFJ hF hqF hc hcard
      obtain ⟨j, hj⟩ : (pre \ F).Nonempty := by
        rw [← Finset.card_pos, hc]; omega
      obtain ⟨hjpre, hjF⟩ := Finset.mem_sdiff.1 hj
      have hjJ := hpreJ hjpre
      have hinfj : ¬ MlFeas t D (insert j F) := by
        intro h
        have := hmax _ (Finset.insert_subset hjJ hFJ) h
        rw [Finset.card_insert_of_notMem hjF] at this
        omega
      obtain ⟨x, hxF, hxpre, hfe⟩ := ml_exchange Jc t D ht pre hpreJ hpreF q htpre htrest F hFJ hF
        j hjpre hjF hinfj
      have hjE : j ∉ F.erase x := fun h => hjF (Finset.mem_of_mem_erase h)
      have hcard' : (insert j (F.erase x)).card = N := by
        rw [Finset.card_insert_of_notMem hjE, Finset.card_erase_of_mem hxF]
        have : 0 < F.card := Finset.card_pos.2 ⟨x, hxF⟩
        omega
      have hsubJ : insert j (F.erase x) ⊆ Jc :=
        Finset.insert_subset hjJ ((Finset.erase_subset _ _).trans hFJ)
      by_cases hxq : x = q
      · subst hxq
        refine ⟨_, hsubJ, hfe, ?_, hcard'⟩
        intro h
        rcases Finset.mem_insert.1 h with h' | h'
        · exact hqpre (h' ▸ hjpre)
        · exact Finset.notMem_erase x F h'
      · apply ih _ hsubJ hfe
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨Ne.symm hxq, hqF⟩)
        · have : pre \ insert j (F.erase x) = (pre \ F).erase j := by
            ext y
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨hy, hy2⟩
              push_neg at hy2
              refine ⟨hy2.1, hy, fun hyF => ?_⟩
              exact hy2.2 (fun hyx => hxpre (hyx ▸ hy)) hyF
            · rintro ⟨hyj, hy, hyF⟩
              refine ⟨hy, ?_⟩
              rintro (h | ⟨_, h⟩)
              · exact hyj h
              · exact hyF h
          rw [this, Finset.card_erase_of_mem hj, hc]; omega
        · exact hcard'
  have hG : ∃ G ⊆ Jc, MlFeas t D G ∧ q ∉ G ∧ G.card = N := by
    by_cases hqF0 : q ∈ F0
    · exact hiter _ F0 (Finset.mem_powerset.1 hF0'.1) hF0'.2 hqF0 rfl rfl
    · exact ⟨F0, Finset.mem_powerset.1 hF0'.1, hF0'.2, hqF0, rfl⟩
  obtain ⟨G, hGJ, hGF, hqG, hGc⟩ := hG
  obtain ⟨AG, hAG, hAGd⟩ := ml_edd_exists D G
  have hAGe : lateSet t D AG = ∅ := by
    apply ml_early_of_feas t D AG hAG.1 hAGd (fun i hi => ht i (hGJ ((hAG.2 i).1 hi)))
    rwa [ml_toFinset_of_sched G AG hAG]
  set R := (Jc \ G).toList with hR
  have hsch : IsSchedule Jc (AG ++ R) := by
    refine ⟨?_, fun x => ?_⟩
    · rw [List.nodup_append]
      refine ⟨hAG.1, Finset.nodup_toList _, ?_⟩
      intro a ha b hb hab
      subst hab
      rw [hR, Finset.mem_toList, Finset.mem_sdiff] at hb
      exact hb.2 ((hAG.2 a).1 ha)
    · rw [List.mem_append, hAG.2 x, hR, Finset.mem_toList, Finset.mem_sdiff]
      constructor
      · rintro (h | h)
        · exact hGJ h
        · exact h.1
      · intro hx; by_cases h : x ∈ G
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
  have hlsub : lateSet t D (AG ++ R) ⊆ Jc \ G := by
    intro j hj
    rw [ml_mem_lateSet] at hj
    obtain ⟨hjm, hlt⟩ := hj
    rcases List.mem_append.1 hjm with h | h
    · rw [ml_ct_append_left t _ _ j h] at hlt
      have : j ∈ lateSet t D AG := (ml_mem_lateSet t D AG j).2 ⟨h, hlt⟩
      rw [hAGe] at this; simp at this
    · rwa [hR, Finset.mem_toList] at h
  have hcS : (lateSet t D (AG ++ R)).card + N ≤ Jc.card := by
    have := Finset.card_le_card hlsub
    have h2 := Finset.card_sdiff_add_card_eq_card hGJ
    omega
  refine ⟨AG ++ R, ⟨hsch, fun l' hl' => ?_⟩, ?_⟩
  · have h1 := hmax _ Finset.sdiff_subset (ml_early_set_feas Jc t D ht l' hl')
    have h2 := ml_card_early Jc t D l' hl'
    omega
  · by_contra hql
    have hsub : insert q G ⊆ Jc \ lateSet t D (AG ++ R) := by
      intro y hy
      rw [Finset.mem_sdiff]
      rcases Finset.mem_insert.1 hy with h | h
      · subst h; exact ⟨hq, hql⟩
      · refine ⟨hGJ h, fun hl => ?_⟩
        have := hlsub hl
        exact (Finset.mem_sdiff.1 this).2 h
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hqG] at h1
    have h2 := hmax _ Finset.sdiff_subset (ml_early_set_feas Jc t D ht _ hsch)
    omega

theorem ml_insert_infeasible (Jc : Finset ι) (t D : ι → ℝ) (ht : ∀ i ∈ Jc, 0 ≤ t i)
    (pre : List ι) (q : ι) (hq : q ∈ Jc) (hqpre : q ∉ pre) (hpreJ : ∀ a ∈ pre, a ∈ Jc)
    (hnd : pre.Nodup) (hdd : pre.Pairwise (fun a b => D a ≤ D b))
    (k : ℕ) (hk₁ : ∀ a ∈ pre.take k, D a ≤ D q) (hk₂ : ∀ a ∈ pre.drop k, D q ≤ D a)
    (hlate : (lateSet t D (pre.take k ++ q :: pre.drop k)).Nonempty) :
    ¬ MlFeas t D (insert q pre.toFinset) := by
  intro hF
  have hperm : (pre.take k ++ q :: pre.drop k).Perm (q :: pre) := by
    have := (List.perm_middle (a := q) (l₁ := pre.take k) (l₂ := pre.drop k))
    rwa [List.take_append_drop] at this
  have hnd' : (pre.take k ++ q :: pre.drop k).Nodup :=
    hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hqpre, hnd⟩)
  have hdd' : (pre.take k ++ q :: pre.drop k).Pairwise (fun a b => D a ≤ D b) := by
    have hsplit := hdd
    rw [← List.take_append_drop k pre, List.pairwise_append] at hsplit
    rw [List.pairwise_append]
    refine ⟨hsplit.1, List.pairwise_cons.2 ⟨hk₂, hsplit.2.1⟩, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.1 hb with h | h
    · subst h; exact hk₁ a ha
    · exact hsplit.2.2 a ha b h
  have := ml_early_of_feas t D _ hnd' hdd'
    (fun i hi => by
      rcases List.mem_cons.1 (hperm.mem_iff.1 hi) with h | h
      · subst h; exact ht _ hq
      · exact ht i (hpreJ i h))
    (by rwa [List.toFinset_eq_of_perm _ _ hperm, List.toFinset_cons])
  rw [this] at hlate
  simp at hlate

theorem selection_list (Jc : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ Jc, 0 ≤ t i)
    (pre : List ι) (q : ι) (hq : q ∈ Jc) (hqpre : q ∉ pre) (hpreJ : ∀ a ∈ pre, a ∈ Jc)
    (hnd : pre.Nodup) (hdd : pre.Pairwise (fun a b => D a ≤ D b))
    (hearly : lateSet t D pre = ∅)
    (htpre : ∀ a ∈ pre, t a ≤ t q) (htrest : ∀ b ∈ Jc, b ∉ pre → b ≠ q → t q ≤ t b)
    (k : ℕ) (hk₁ : ∀ a ∈ pre.take k, D a ≤ D q) (hk₂ : ∀ a ∈ pre.drop k, D q ≤ D a)
    (hlate : (lateSet t D (pre.take k ++ q :: pre.drop k)).Nonempty) :
    ∃ S : List ι, IsOptimal t D Jc S ∧ q ∈ lateSet t D S := by
  apply selection_core Jc t D ht pre.toFinset (fun a ha => hpreJ a (List.mem_toFinset.1 ha))
    (ml_feas_of_sched t D pre hnd (fun i hi => ht i (hpreJ i hi)) hearly) q hq
    (by simpa using hqpre) (fun a ha => htpre a (List.mem_toFinset.1 ha))
    (fun b hb hb2 hb3 => htrest b hb (by simpa using hb2) hb3)
  exact ml_insert_infeasible Jc t D ht pre q hq hqpre hpreJ hnd hdd k hk₁ hk₂ hlate

end base
end MooreLateJobs.NumLate

open MooreLateJobs.NumLate
open MooreLateJobs

theorem solution {ι : Type*} [DecidableEq ι] (Jc : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ Jc, 0 ≤ t i) (htD : ∀ i ∈ Jc, t i ≤ D i)
    (pre : List ι) (q : ι) (hq : q ∈ Jc) (hqpre : q ∉ pre) (hpreJ : ∀ a ∈ pre, a ∈ Jc)
    (hnd : pre.Nodup) (hdd : pre.Pairwise (fun a b => D a ≤ D b))
    (hearly : lateSet t D pre = ∅)
    (htpre : ∀ a ∈ pre, t a ≤ t q) (htrest : ∀ b ∈ Jc, b ∉ pre → b ≠ q → t q ≤ t b)
    (k : ℕ) (hk₁ : ∀ a ∈ pre.take k, D a ≤ D q) (hk₂ : ∀ a ∈ pre.drop k, D q ≤ D a)
    (hlate : q ∈ lateSet t D (pre.take k ++ q :: pre.drop k)) :
    ∃ S : List ι, IsOptimal t D Jc S ∧ q ∈ lateSet t D S := by
  exact selection_list Jc t D ht pre q hq hqpre hpreJ hnd hdd hearly htpre htrest k hk₁ hk₂ ⟨q, hlate⟩
