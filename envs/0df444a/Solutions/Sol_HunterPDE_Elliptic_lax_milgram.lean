-- Prove2me | solution 1 for HunterPDE.Elliptic.lax_milgram
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:10:43.802743+00:00
-- url     : https://prove2.me/submissions/73039237-f626-4f99-abda-19b0a6f569e3

import Mathlib

set_option autoImplicit false

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (ha₁ : ∀ u : H, C₁ * ‖u‖ ^ 2 ≤ a u u) (ha₂ : ∀ u v : H, |a u v| ≤ C₂ * ‖u‖ * ‖v‖)
    (f : StrongDual ℝ H) :
    ∃! u : H, ∀ v : H, f v = a u v := by
  let B : H →L[ℝ] H →L[ℝ] ℝ := LinearMap.mkContinuous₂ a C₂ (fun x y => by
    rw [Real.norm_eq_abs]; exact ha₂ x y)
  have hB : ∀ x y, B x y = a x y := fun x y => rfl
  have hcoer : IsCoercive B := ⟨C₁, hC₁, fun u => by
    rw [hB, mul_assoc, ← sq]; exact ha₁ u⟩
  let E := hcoer.continuousLinearEquivOfBilin
  let g : H := (InnerProductSpace.toDual ℝ H).symm f
  refine ⟨E.symm g, fun v => ?_, fun w hw => ?_⟩
  · rw [← hB, ← IsCoercive.continuousLinearEquivOfBilin_apply hcoer,
      ContinuousLinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
  · have h1 : g = E w := hcoer.unique_continuousLinearEquivOfBilin (fun v => by
      rw [InnerProductSpace.toDual_symm_apply, hw v, hB])
    rw [h1, ContinuousLinearEquiv.symm_apply_apply]
