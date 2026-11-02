-- Prove2me | solution 1 for IntertempDUI.Finite.lemma_B1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:09:51.019547+00:00
-- url     : https://prove2.me/submissions/37ce6f79-7f95-402f-82df-3313d86d98a5

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Content

open IntertempDUI.Finite

namespace IDUIB1

lemma span_empty (T : ℝ) : IsTimeSpan (∅ : Set (Time T)) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩

lemma span_univ (T : ℝ) (hT : 0 < T) : IsTimeSpan (Set.univ : Set (Time T)) := by
  refine ⟨1, fun _ => 0, fun _ => T, fun _ => ⟨le_refl _, hT, le_refl _⟩, ?_, ?_⟩
  · intro i j hij
    exact absurd hij (by omega)
  · ext t
    simp only [Set.mem_univ, Set.mem_iUnion, bracket, Set.mem_ofPred_eq, true_iff]
    refine ⟨0, ?_, ?_⟩
    · rcases lt_or_eq_of_le t.2.1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨trivial, h.symm⟩
    · rcases lt_or_eq_of_le t.2.2 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨trivial, h⟩

end IDUIB1

open IDUIB1 in
theorem solution {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (u : X → ℝ) (hu : Continuous u)
    (hrep : ∀ x y : X, sy pref x y ↔ u y ≤ u x)
    (hM : MinEqn A pref) :
    ∀ a ∈ A, Comeasurable (u ∘ a) := by
  intro a ha r
  -- intermediate value: if `r` is attained between two values of `u`, it is a value of `u`
  have ivt : ∀ x1 x2 : X, u x1 ≤ r → r ≤ u x2 → ∃ x, u x = r := by
    intro x1 x2 h1 h2
    have := isPreconnected_univ.intermediate_value (Set.mem_univ x1) (Set.mem_univ x2)
      hu.continuousOn ⟨h1, h2⟩
    obtain ⟨x, -, hx⟩ := this
    exact ⟨x, hx⟩
  constructor
  · by_cases hlow : ∀ x, r < u x
    · have : {t | (u ∘ a) t ≤ r} = (∅ : Set (Time T)) := by
        ext t; simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_le]; exact hlow _
      rw [this, interior_empty]; exact span_empty T
    push Not at hlow
    obtain ⟨x1, hx1⟩ := hlow
    by_cases hhigh : ∀ x, u x ≤ r
    · have : {t | (u ∘ a) t ≤ r} = (Set.univ : Set (Time T)) := by
        ext t; simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact hhigh _
      rw [this, interior_univ]; exact span_univ T hT
    push Not at hhigh
    obtain ⟨x2, hx2⟩ := hhigh
    obtain ⟨x, rfl⟩ := ivt x1 x2 hx1 hx2.le
    have : {t | (u ∘ a) t ≤ u x} = {t | sy pref x (a t)} := by
      ext t; simp only [Function.comp, Set.mem_ofPred_eq]; exact (hrep x (a t)).symm
    rw [this]; exact (hM x a ha).2
  · by_cases hlow : ∀ x, u x < r
    · have : {t | r ≤ (u ∘ a) t} = (∅ : Set (Time T)) := by
        ext t; simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_le]; exact hlow _
      rw [this, interior_empty]; exact span_empty T
    push Not at hlow
    obtain ⟨x2, hx2⟩ := hlow
    by_cases hhigh : ∀ x, r ≤ u x
    · have : {t | r ≤ (u ∘ a) t} = (Set.univ : Set (Time T)) := by
        ext t; simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact hhigh _
      rw [this, interior_univ]; exact span_univ T hT
    push Not at hhigh
    obtain ⟨x1, hx1⟩ := hhigh
    obtain ⟨x, rfl⟩ := ivt x1 x2 hx1.le hx2
    have : {t | u x ≤ (u ∘ a) t} = {t | sy pref (a t) x} := by
      ext t; simp only [Function.comp, Set.mem_ofPred_eq]; exact (hrep (a t) x).symm
    rw [this]; exact (hM x a ha).1
