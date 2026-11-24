-- Prove2me | solution 1 for LinearIdentifiability.diversity_requires_enough_classes
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T15:09:20.023962+00:00
-- url     : https://prove2.me/submissions/2b24807c-a219-435b-8da9-6f3de393a130

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix
namespace LinearIdentifiability


theorem diversity_requires_enough_classes {Y : Type*} {M : ℕ} (hM : 0 < M)
    (g : Y → Fin M → ℝ) (S : Finset Y) (a b : Fin M → Y)
    (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S) (hL : IsUnit (diffMatrix g a b).det) :
    M + 1 ≤ S.card := by
  classical
  have hA : IsUnit (diffMatrix g a b) := (Matrix.isUnit_iff_isUnit_det _).mpr hL
  have hli : LinearIndependent ℝ (fun i => (diffMatrix g a b)ᵀ i) :=
    Matrix.linearIndependent_cols_of_isUnit hA
  set y0 := a ⟨0, hM⟩ with hy0
  have hy0S : y0 ∈ S := ha _
  set s : Finset (Fin M → ℝ) := (S.erase y0).image (fun y => g y - g y0) with hs
  have hmem : ∀ y ∈ S, g y - g y0 ∈ Submodule.span ℝ (s : Set (Fin M → ℝ)) := by
    intro y hy
    by_cases h : y = y0
    · subst h; simp
    · apply Submodule.subset_span
      simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase]
      exact ⟨y, ⟨h, hy⟩, rfl⟩
  have hcol : ∀ i, (diffMatrix g a b)ᵀ i = (g (a i) - g y0) - (g (b i) - g y0) := by
    intro i; ext j; simp [diffMatrix, Matrix.transpose_apply]
  have hle : Submodule.span ℝ (Set.range fun i => (diffMatrix g a b)ᵀ i) ≤
      Submodule.span ℝ (s : Set (Fin M → ℝ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show (diffMatrix g a b)ᵀ i ∈ (Submodule.span ℝ (s : Set (Fin M → ℝ)) : Set (Fin M → ℝ))
    rw [hcol]
    exact Submodule.sub_mem _ (hmem _ (ha i)) (hmem _ (hb i))
  have h1 := finrank_span_eq_card hli
  have h2 := Submodule.finrank_mono hle
  have h3 := finrank_span_finset_le_card (R := ℝ) s
  unfold Set.finrank at h3
  have h4 : s.card ≤ S.card - 1 := by
    calc s.card ≤ (S.erase y0).card := Finset.card_image_le
      _ = S.card - 1 := Finset.card_erase_of_mem hy0S
  have h5 : 0 < S.card := Finset.card_pos.mpr ⟨y0, hy0S⟩
  simp only [Fintype.card_fin] at h1
  omega


end LinearIdentifiability

open LinearIdentifiability in
theorem solution {Y : Type*} {M : ℕ} (hM : 0 < M)
    (g : Y → Fin M → ℝ) (S : Finset Y) (a b : Fin M → Y)
    (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S) (hL : IsUnit (diffMatrix g a b).det) :
    M + 1 ≤ S.card := by
  classical
  have hA : IsUnit (diffMatrix g a b) := (Matrix.isUnit_iff_isUnit_det _).mpr hL
  have hli : LinearIndependent ℝ (fun i => (diffMatrix g a b)ᵀ i) :=
    Matrix.linearIndependent_cols_of_isUnit hA
  set y0 := a ⟨0, hM⟩ with hy0
  have hy0S : y0 ∈ S := ha _
  set s : Finset (Fin M → ℝ) := (S.erase y0).image (fun y => g y - g y0) with hs
  have hmem : ∀ y ∈ S, g y - g y0 ∈ Submodule.span ℝ (s : Set (Fin M → ℝ)) := by
    intro y hy
    by_cases h : y = y0
    · subst h; simp
    · apply Submodule.subset_span
      simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase]
      exact ⟨y, ⟨h, hy⟩, rfl⟩
  have hcol : ∀ i, (diffMatrix g a b)ᵀ i = (g (a i) - g y0) - (g (b i) - g y0) := by
    intro i; ext j; simp [diffMatrix, Matrix.transpose_apply]
  have hle : Submodule.span ℝ (Set.range fun i => (diffMatrix g a b)ᵀ i) ≤
      Submodule.span ℝ (s : Set (Fin M → ℝ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show (diffMatrix g a b)ᵀ i ∈ (Submodule.span ℝ (s : Set (Fin M → ℝ)) : Set (Fin M → ℝ))
    rw [hcol]
    exact Submodule.sub_mem _ (hmem _ (ha i)) (hmem _ (hb i))
  have h1 := finrank_span_eq_card hli
  have h2 := Submodule.finrank_mono hle
  have h3 := finrank_span_finset_le_card (R := ℝ) s
  unfold Set.finrank at h3
  have h4 : s.card ≤ S.card - 1 := by
    calc s.card ≤ (S.erase y0).card := Finset.card_image_le
      _ = S.card - 1 := Finset.card_erase_of_mem hy0S
  have h5 : 0 < S.card := Finset.card_pos.mpr ⟨y0, hy0S⟩
  simp only [Fintype.card_fin] at h1
  omega

