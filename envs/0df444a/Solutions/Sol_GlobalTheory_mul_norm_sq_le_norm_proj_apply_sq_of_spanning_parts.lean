-- Prove2me | solution 1 for GlobalTheory.mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:35.691533+00:00
-- url     : https://prove2.me/submissions/18023101-e40f-496d-86ef-b5ab329d6760

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulNormSqLeNormProjApplySqOfSpanningParts
import Theorems.Thm_GlobalTheory_mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X Y ι : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ), 0 < m → LinearMap.adjoint e = e → (∀ y, e (e y) = e y) → (⨆ k, P k) = ⊤ → (∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) → ∀ x ∈ (LinearMap.ker (e ∘ₗ T))ᗮ, m * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 := by
  intro X Y ι _ _ _ _ _ _ T e P m hm he hee hP hl x hx
  rw [LinearMap.orthogonal_ker] at hx
  obtain ⟨w, hw⟩ := hx
  rw [LinearMap.adjoint_comp, he, LinearMap.comp_apply] at hw
  set u := e w with hu
  have h1 := mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts T P m hP hl u
  rw [hw] at h1
  have h2 : ⟪x, x⟫_ℂ = ⟪u, e (T x)⟫_ℂ := by
    have : ⟪u, e (T x)⟫_ℂ = ⟪e u, T x⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_left e, he]
    rw [this, hu, hee, ← hu, ← LinearMap.adjoint_inner_left T, hw]
  have h3 : ‖x‖ ^ 2 ≤ ‖u‖ * ‖e (T x)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) u (e (T x))
    rw [← h2, inner_self_eq_norm_sq_to_K] at h
    simpa using h
  by_cases hx0 : x = 0
  · simp [hx0]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have h4 : (‖x‖ ^ 2) ^ 2 ≤ (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
  have h5 : (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by
    calc (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 = m * (‖x‖ ^ 2) ^ 2 := by ring
      _ ≤ m * (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
      _ = ‖e (T x)‖ ^ 2 * (m * ‖u‖ ^ 2) := by ring
      _ ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
  exact le_of_mul_le_mul_right h5 hpos
end GlobalTheory
