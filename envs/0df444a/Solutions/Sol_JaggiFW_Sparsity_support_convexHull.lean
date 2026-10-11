-- Prove2me | solution 1 for JaggiFW.Sparsity.support_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:40:57.868032+00:00
-- url     : https://prove2.me/submissions/2c8bfd41-3d40-464c-9501-c1e82262cae4

import Mathlib
import Definitions.Def_JaggiFW_Sparsity_Setting

open JaggiFW.Sparsity

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Set E) (y : E) :
    (∀ c : ℝ, (∀ s ∈ convexHull ℝ A, inner ℝ s y ≤ c) ↔
      (∀ a ∈ A, inner ℝ a y ≤ c)) ∧
    (A.Finite → A.Nonempty →
      ∃ a ∈ A, IsGreatest ((fun s => inner ℝ s y) '' convexHull ℝ A) (inner ℝ a y)) := by
  have bound (c : ℝ) (h : ∀ a ∈ A, inner ℝ a y ≤ c) :
      ∀ s ∈ convexHull ℝ A, inner ℝ s y ≤ c := by
    apply convexHull_min h
    intro a ha b hb α β hα hβ hsum
    change inner ℝ (α • a + β • b) y ≤ c
    simp only [inner_add_left, inner_smul_left, conj_trivial]
    calc
      α * inner ℝ a y + β * inner ℝ b y ≤ α * c + β * c :=
        add_le_add (mul_le_mul_of_nonneg_left ha hα) (mul_le_mul_of_nonneg_left hb hβ)
      _ = c := by rw [← add_mul, hsum, one_mul]
  refine ⟨fun c => ⟨fun h a ha => h a (subset_convexHull ℝ A ha), bound c⟩, ?_⟩
  intro hfinite hne
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image A (fun s => inner ℝ s y) hfinite hne
  refine ⟨a, ha, ⟨⟨a, subset_convexHull ℝ A ha, rfl⟩, ?_⟩⟩
  rintro r ⟨s, hs, rfl⟩
  exact bound _ hmax s hs
