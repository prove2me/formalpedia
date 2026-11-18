-- Prove2me | solution 1 for NearLogSetCover966.Main.separator_composition_correct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:00:43.523206+00:00
-- url     : https://prove2.me/submissions/520d370d-1c0a-4412-a4a8-e1a498623734

import Definitions.Def_NearLogSetCover966_SeparatorComposition
set_option autoImplicit false
namespace NearLogSetCover966.Main

theorem compose_size {D d₁ d₂ : ℕ}
    (H₁ : HashFamily D d₁) (H₂ : HashFamily d₁ d₂) :
    (H₁.compose H₂).maps.length ≤ H₁.maps.length * H₂.maps.length := by
  classical
  calc
    _ ≤ (H₁.maps.flatMap fun a => H₂.maps.map fun b => b * a).length := List.Sublist.length_le (List.dedup_sublist _)
    _ = H₁.maps.length * H₂.maps.length := by simp

theorem compose_avoids {D d₁ d₂ : ℕ} (A : ℝ)
    (H₁ : HashFamily D d₁) (H₂ : HashFamily d₁ d₂)
    (h₁ : H₁.avoids A) (h₂ : H₂.avoids A) :
    (H₁.compose H₂).avoids A := by
  classical
  intro Z hZ hcard
  obtain ⟨a, ha, haz⟩ := h₁ Z hZ hcard
  have hzero : (0 : Vec d₁) ∉ Z.image a.mulVec := by
    intro h
    obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp h
    exact haz z hz hza
  have himage : ((Z.image a.mulVec).card : ℝ) ≤ A :=
    (Nat.cast_le.mpr (Finset.card_image_le)).trans hcard
  obtain ⟨b, hb, hbz⟩ := h₂ (Z.image a.mulVec) hzero himage
  refine ⟨b * a, ?_, ?_⟩
  · simp only [HashFamily.compose, List.mem_dedup, List.mem_flatMap, List.mem_map]
    exact ⟨a, ha, b, hb, rfl⟩
  · intro z hz
    have h := hbz (a.mulVec z) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    simpa only [Matrix.mulVec_mulVec] using h

end NearLogSetCover966.Main
open NearLogSetCover966.Main

theorem solution {D d₁ d₂ : ℕ} (A : ℝ)
    (H₁ : HashFamily D d₁) (H₂ : HashFamily d₁ d₂)
    (h₁ : H₁.avoids A) (h₂ : H₂.avoids A) :
    (H₁.compose H₂).avoids A ∧
      (H₁.compose H₂).maps.length ≤ H₁.maps.length * H₂.maps.length := by
  exact ⟨compose_avoids A H₁ H₂ h₁ h₂, compose_size H₁ H₂⟩

