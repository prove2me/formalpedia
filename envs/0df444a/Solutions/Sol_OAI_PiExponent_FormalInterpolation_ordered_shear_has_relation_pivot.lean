-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.ordered_shear_has_relation_pivot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:09:40.83412+00:00
-- url     : https://prove2.me/submissions/76ff25f2-dfdf-44d4-ade4-0fc59dfd7b14

import Mathlib

open scoped BigOperators

theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : Nat} (u v : Fin (m + 1) → V) (t : K) (ht : t ≠ 0)
    (hzero : v 0 = t • u 0 + ∑ j : Fin m, u j.succ)
    (hsucc : ∀ j : Fin m, v j.succ = u j.succ)
    (hnonzero : ∃ i, u i ≠ 0)
    (hexclusion :
      ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
        (LinearIndependent K (fun i : A => u i) ∧
          Submodule.span K (Set.range (fun i : A => u i)) =
            Submodule.span K (Set.range u)) →
        (LinearIndependent K (fun i : B => v i) ∧
          Submodule.span K (Set.range (fun i : B => v i)) =
            Submodule.span K (Set.range v)) →
        ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
          (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ i : Fin (m + 1),
      ∀ a : Fin (m + 1) → K, (∑ j, a j • v j) = 0 → a i = 0 := by
  classical
  by_contra hc
  push Not at hc
  have hvu : ∀ j : Fin (m + 1), j ≠ 0 → v j = u j := by
    intro j hj
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    exact hsucc j'
  -- the largest index with u ≠ 0
  have hne : (Finset.univ.filter (fun j => u j ≠ 0)).Nonempty := by
    obtain ⟨i, hi⟩ := hnonzero; exact ⟨i, by simp [hi]⟩
  set i := (Finset.univ.filter (fun j => u j ≠ 0)).max' hne with hi_def
  have hui : u i ≠ 0 := by
    have := Finset.max'_mem _ hne
    rw [← hi_def] at this; simpa using this
  have hbig : ∀ j, i < j → u j = 0 := by
    intro j hj
    by_contra h
    have : j ≤ i := Finset.le_max' _ j (by simp [h])
    exact absurd hj (not_lt.mpr this)
  by_cases hi0 : i = 0
  · obtain ⟨a, ha, ha0⟩ := hc 0
    have hz : ∀ j : Fin m, u j.succ = 0 := fun j => hbig _ (by rw [hi0]; exact Fin.succ_pos j)
    rw [Fin.sum_univ_succ] at ha
    simp only [hsucc, hz, smul_zero, Finset.sum_const_zero, add_zero, hzero] at ha
    rw [smul_smul] at ha
    rcases smul_eq_zero.mp ha with h | h
    · exact mul_ne_zero ha0 ht h
    · exact hui (hi0 ▸ h)
  -- span equality
  have hspan : Submodule.span K (Set.range u) = Submodule.span K (Set.range v) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hj : j = 0
      · subst hj
        have : u 0 = t⁻¹ • (v 0 - ∑ j : Fin m, v j.succ) := by
          rw [hzero]; simp only [hsucc, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [this]
        refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩)
          (Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, rfl⟩))
      · rw [← hvu j hj]; exact Submodule.subset_span ⟨j, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hj : j = 0
      · subst hj
        rw [hzero]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, rfl⟩)
      · rw [hvu j hj]; exact Submodule.subset_span ⟨j, rfl⟩
  -- basis A of u containing i
  have hLi : LinearIndepOn K u ({i} : Set (Fin (m + 1))) := (linearIndepOn_singleton_iff K).mpr hui
  obtain ⟨b, -, hib, hbspan, hbli⟩ := exists_linearIndepOn_extension hLi (Set.subset_univ _)
  -- basis B of v avoiding i
  obtain ⟨a, ha, hai⟩ := hc i
  obtain ⟨b', hb't, -, hb'span, hb'li⟩ := exists_linearIndepOn_extension (v := v)
    (linearIndepOn_empty K v) (Set.empty_subset {j | j ≠ i})
  have hvi : v i ∈ Submodule.span K (v '' b') := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at ha
    have h2 := eq_neg_of_add_eq_zero_left ha
    have : v i = (a i)⁻¹ • -(∑ j ∈ Finset.univ.erase i, a j • v j) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ hai, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.neg_mem _
      (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_))
    exact hb'span ⟨j, Finset.ne_of_mem_erase hj, rfl⟩
  have hspanA : Submodule.span K (Set.range (fun j : (b.toFinset : Finset _) => u j)) =
      Submodule.span K (Set.range u) := by
    apply le_antisymm
    · exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have := hbspan ⟨j, Set.mem_univ _, rfl⟩
      have e : Set.range (fun j : (b.toFinset : Finset _) => u j) = u '' b := by
        ext x; simp
      rw [e]; exact this
  have hspanB : Submodule.span K (Set.range (fun j : (b'.toFinset : Finset _) => v j)) =
      Submodule.span K (Set.range v) := by
    apply le_antisymm
    · exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have : v j ∈ Submodule.span K (v '' b') := by
        by_cases hj : j = i
        · rw [hj]; exact hvi
        · exact hb'span ⟨j, hj, rfl⟩
      have e : Set.range (fun j : (b'.toFinset : Finset _) => v j) = v '' b' := by
        ext x; simp
      rw [e]; exact this
  have hliA : LinearIndependent K (fun j : (b.toFinset : Finset _) => u j) := by
    have : LinearIndepOn K u (↑b.toFinset : Set (Fin (m + 1))) := by rw [Set.coe_toFinset]; exact hbli
    exact this
  have hliB : LinearIndependent K (fun j : (b'.toFinset : Finset _) => v j) := by
    have : LinearIndepOn K v (↑b'.toFinset : Set (Fin (m + 1))) := by rw [Set.coe_toFinset]; exact hb'li
    exact this
  have hcard : b.toFinset.card = b'.toFinset.card := by
    have h1 := finrank_span_eq_card hliA
    have h2 := finrank_span_eq_card hliB
    rw [hspanA, hspan] at h1
    rw [hspanB] at h2
    simp only [Fintype.card_coe] at h1 h2
    omega
  refine hexclusion b.toFinset b'.toFinset hcard ⟨hliA, hspanA⟩ ⟨hliB, hspanB⟩ i hi0
    (by simpa using hib) (by simpa using fun h => hb't h rfl) ?_
  intro j hj
  have hu0 := hbig j hj
  have hj0 : j ≠ 0 := fun h => by rw [h] at hj; exact absurd hj (Fin.not_lt_zero _)
  have hv0 : v j = 0 := by rw [hvu j hj0, hu0]
  constructor
  · intro hjA
    exact absurd hu0 (hliA.ne_zero ⟨j, hjA⟩)
  · intro hjB
    exact absurd hv0 (hliB.ne_zero ⟨j, hjB⟩)
