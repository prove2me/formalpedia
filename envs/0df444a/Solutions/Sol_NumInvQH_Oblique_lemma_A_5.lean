-- Prove2me | solution 1 for NumInvQH.Oblique.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:32:18.547946+00:00
-- url     : https://prove2.me/submissions/eed7ca33-4e55-4f9d-8a19-2a6377bb8fb2

import Mathlib

open Submodule

theorem numinv_key {n : ℕ} (L M : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Mᗮ.map (L.starProjection : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      = L ⊓ (L ⊓ M)ᗮ := by
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨starProjection_apply_mem L b, ?_⟩
    have hb' : b ∈ Mᗮ := hb
    show L.starProjection b ∈ (L ⊓ M)ᗮ
    rw [mem_orthogonal]
    intro z hz
    have h1 : L.starProjection z = z := starProjection_eq_self_iff.mpr hz.1
    show inner ℝ z (L.starProjection b) = 0
    rw [← inner_starProjection_left_eq_right, h1]
    exact (mem_orthogonal M b).1 hb' z hz.2
  · rintro w ⟨hwL, hw⟩
    have hLM : L ⊓ M = (Lᗮ ⊔ Mᗮ)ᗮ := by
      rw [← inf_orthogonal, orthogonal_orthogonal, orthogonal_orthogonal]
    rw [hLM, orthogonal_orthogonal] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.1 hw
    refine ⟨b, hb, ?_⟩
    have h1 : L.starProjection (a + b) = a + b := starProjection_eq_self_iff.mpr hwL
    have h2 : L.starProjection a = 0 := (starProjection_apply_eq_zero_iff L).mpr ha
    rw [map_add, h2, zero_add] at h1
    exact h1

theorem solution {n : ℕ} (L M : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    let PL : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := L.starProjection
    (L ⊓ M) ⊔ (L ⊓ (L ⊓ M)ᗮ) = L ∧ (L ⊓ M) ⟂ (L ⊓ (L ⊓ M)ᗮ) ∧
    (L ⊓ M) ⊔ Mᗮ.map PL = L ∧ (L ⊓ M) ⟂ Mᗮ.map PL := by
  intro PL
  have hkey : Mᗮ.map PL = L ⊓ (L ⊓ M)ᗮ := numinv_key L M
  have h1 : (L ⊓ M) ⊔ (L ⊓ (L ⊓ M)ᗮ) = L := by
    rw [inf_comm L (L ⊓ M)ᗮ]
    exact sup_orthogonal_inf_of_hasOrthogonalProjection inf_le_left
  have h2 : (L ⊓ M) ⟂ (L ⊓ (L ⊓ M)ᗮ) :=
    (isOrtho_orthogonal_right (L ⊓ M)).mono_right inf_le_right
  rw [hkey]
  exact ⟨h1, h2, h1, h2⟩
