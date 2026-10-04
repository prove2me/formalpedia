-- Prove2me | solution 1 for HardyFiveAxioms.reversible_maps_pure_to_pure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:53:06.455116+00:00
-- url     : https://prove2.me/submissions/33f5cb92-bf24-4975-be16-ad4439341d5a

import Mathlib
import Definitions.Def_hardy2001_states

set_option autoImplicit false

open HardyFiveAxioms Matrix in
theorem solution {K : ℕ} (S : Set (Fin K → ℝ))
    (Z : Matrix (Fin K) (Fin K) ℝ) (hZ : IsUnit Z)
    (hZS : ∀ p ∈ S, Z *ᵥ p ∈ S) (hZinvS : ∀ p ∈ S, Z⁻¹ *ᵥ p ∈ S)
    (p : Fin K → ℝ) (hp : p ∈ pureStates S) :
    Z *ᵥ p ∈ pureStates S := by
  have hdet : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det Z).mp hZ
  have h1 : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hdet
  have h2 : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hdet
  let f : (Fin K → ℝ) ≃ₗ[ℝ] (Fin K → ℝ) :=
    LinearEquiv.ofLinear (Matrix.mulVecLin Z) (Matrix.mulVecLin Z⁻¹)
      (LinearMap.ext fun v => by
        show Z *ᵥ (Z⁻¹ *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec])
      (LinearMap.ext fun v => by
        show Z⁻¹ *ᵥ (Z *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec])
  have hf : ∀ v, f v = Z *ᵥ v := fun v => rfl
  have himg : f '' S = S := by
    ext q
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [hf]; exact hZS r hr
    · intro hq
      refine ⟨Z⁻¹ *ᵥ q, hZinvS q hq, ?_⟩
      rw [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  unfold pureStates at hp ⊢
  obtain ⟨hpe, hp0⟩ := hp
  refine ⟨?_, ?_⟩
  · have : f p ∈ f '' Set.extremePoints ℝ S := ⟨p, hpe, rfl⟩
    rw [image_extremePoints, himg] at this
    simpa [hf] using this
  · intro h
    apply hp0
    have h' : f p = f 0 := by rw [map_zero]; simpa [hf] using h
    simpa using f.injective h'
