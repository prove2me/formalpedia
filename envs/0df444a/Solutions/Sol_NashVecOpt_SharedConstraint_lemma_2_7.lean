-- Prove2me | solution 1 for NashVecOpt.SharedConstraint.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:47:46.795725+00:00
-- url     : https://prove2.me/submissions/2105a924-5490-4af7-9a08-557bd224451c

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

open NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

theorem nvo_mem_coneI (i : ι) (z : (∀ j, E j) × (ι → ℝ)) :
    z ∈ coneI (E := E) i ↔ (∀ j, j ≠ i → z.1 j = 0) ∧ 0 ≤ z.2 i := by
  unfold coneI
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h1 j
      simpa [hj] using this
    · have := h2 i
      simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = i
      · subst hj; simp
      · simpa [hj] using h1 j hj
    · by_cases hj : j = i
      · subst hj; simpa using h2
      · simp [hj]

theorem nvo_mem_cone (z : (∀ j, E j) × (ι → ℝ)) :
    z ∈ orderCone (E := E) ↔ ∃ i, z ∈ coneI (E := E) i := by
  simp only [nvo_mem_coneI]
  rfl

theorem nvo_eq_update (xs x : ∀ j, E j) (i : ι) (h : ∀ j, j ≠ i → x j = xs j) :
    x = Function.update xs i (x i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, h j hj]

theorem solution (hN : 2 ≤ Fintype.card ι) (f : ι → (∀ j, E j) → ℝ)
    (X : Set (∀ j, E j)) :
    vArgMin (orderCone (E := E)) (obj f) X =
      ⋂ i, vArgMin (coneI (E := E) i) (obj f) X := by
  have hne : Nonempty ι := by
    rw [← Fintype.card_pos_iff]; omega
  -- common characterization
  -- Both sides equal NE f X
  have hL : vArgMin (orderCone (E := E)) (obj f) X = NE f X := by
    ext xs
    simp only [vArgMin, NE, coneLE, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxs, h⟩
      refine ⟨hxs, fun i xi hx => ?_⟩
      by_contra hlt
      push_neg at hlt
      have h1 := h _ hx (by
        rw [nvo_mem_cone]
        refine ⟨i, (nvo_mem_coneI _ _).2 ⟨fun j hj => ?_, ?_⟩⟩
        · simp [obj, hj]
        · simp [obj]; linarith)
      rw [nvo_mem_cone] at h1
      obtain ⟨k, hk⟩ := h1
      rw [nvo_mem_coneI] at hk
      obtain ⟨hk1, hk2⟩ := hk
      by_cases hki : xi = xs i
      · subst hki
        simp at hlt
      · have hik : k = i := by
          by_contra hne'
          have := hk1 i (Ne.symm hne')
          apply hki
          simpa [obj, hne'] using (sub_eq_zero.1 this).symm |>.symm
        subst hik
        simp [obj] at hk2
        linarith
    · rintro ⟨hxs, h⟩
      refine ⟨hxs, fun x hx hle => ?_⟩
      rw [nvo_mem_cone] at hle ⊢
      obtain ⟨i, hi⟩ := hle
      rw [nvo_mem_coneI] at hi
      obtain ⟨hi1, hi2⟩ := hi
      have hx' : ∀ j, j ≠ i → x j = xs j := by
        intro j hj
        have := hi1 j hj
        simp [obj] at this
        exact (sub_eq_zero.1 this).symm
      have hxu := nvo_eq_update xs x i hx'
      have hle2 := h i (x i) (hxu ▸ hx)
      refine ⟨i, (nvo_mem_coneI _ _).2 ⟨fun j hj => ?_, ?_⟩⟩
      · simp [obj, hx' j hj]
      · simp [obj]
        have : f i x = f i (Function.update xs i (x i)) := by rw [← hxu]
        simp [obj] at hi2
        linarith
  rw [hL]
  ext xs
  simp only [Set.mem_iInter]
  constructor
  · rintro ⟨hxs, h⟩ i
    simp only [vArgMin, coneLE, Set.mem_setOf_eq]
    refine ⟨hxs, fun x hx hle => ?_⟩
    rw [nvo_mem_coneI] at hle ⊢
    obtain ⟨hi1, hi2⟩ := hle
    have hx' : ∀ j, j ≠ i → x j = xs j := by
      intro j hj
      have := hi1 j hj
      simp [obj] at this
      exact (sub_eq_zero.1 this).symm
    have hxu := nvo_eq_update xs x i hx'
    have hle2 := h i (x i) (hxu ▸ hx)
    refine ⟨fun j hj => ?_, ?_⟩
    · simp [obj, hx' j hj]
    · simp [obj]
      have : f i x = f i (Function.update xs i (x i)) := by rw [← hxu]
      simp [obj] at hi2
      linarith
  · intro h
    obtain ⟨i0⟩ := hne
    refine ⟨(h i0).1, fun i xi hx => ?_⟩
    by_contra hlt
    push_neg at hlt
    have h1 := (h i).2 _ hx (by
      rw [coneLE, nvo_mem_coneI]
      refine ⟨fun j hj => ?_, ?_⟩
      · simp [obj, hj]
      · simp [obj]; linarith)
    rw [coneLE, nvo_mem_coneI] at h1
    obtain ⟨_, hk2⟩ := h1
    simp [obj] at hk2
    linarith
