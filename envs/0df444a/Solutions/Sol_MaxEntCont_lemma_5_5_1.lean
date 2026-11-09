-- Prove2me | solution 1 for MaxEntCont.lemma_5_5_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T15:13:01.373425+00:00
-- url     : https://prove2.me/submissions/d74aa64f-edc5-4d33-8ab6-2b4fec53eba0

import Mathlib
import Definitions.Def_TriangleFace

open OAI.CanonicalFace198

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (hKc : IsCompact K) (hKv : Convex ℝ K) (f : X →ₗ[ℝ] Y)
    (w : Y) (hw : w ∈ f '' K) (v : X) (hv : v ∈ K) (hfv : f v = w) :
    f '' minFace K v ⊆ minFace (f '' K) w := by
  rintro _ ⟨y, hy, rfl⟩
  unfold minFace at hy ⊢
  rw [Set.mem_sInter] at hy ⊢
  rintro F' ⟨hF'c, hF'e, hwF'⟩
  have hF : K ∩ f ⁻¹' F' ∈ facesThrough K v := by
    refine ⟨hKv.inter (hF'c.linear_preimage f), ⟨Set.inter_subset_left, ?_⟩, ⟨hv, ?_⟩⟩
    · intro x₁ hx₁ x₂ hx₂ x hx hseg
      have hseg' : f x ∈ openSegment ℝ (f x₁) (f x₂) := by
        obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
        exact ⟨a, b, ha, hb, hab, by simp⟩
      exact Set.mem_inter hx₁
        (hF'e.2 (Set.mem_image_of_mem f hx₁) (Set.mem_image_of_mem f hx₂) hx.2 hseg')
    · show f v ∈ F'
      rw [hfv]; exact hwF'
  exact (hy _ hF).2
