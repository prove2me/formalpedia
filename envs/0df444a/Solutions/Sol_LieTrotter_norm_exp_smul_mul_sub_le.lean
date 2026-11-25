-- Prove2me | solution 1 for LieTrotter.norm_exp_smul_mul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:57:46.896959+00:00
-- url     : https://prove2.me/submissions/d5317793-1ce3-4d47-b2bb-3116042b2ccd

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator
public import Theorems.Thm_LieTrotter_norm_exp_smul_le
public import Theorems.Thm_LieTrotter_hasDerivAt_exp_const_sub_smul

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • A) * B - B * exp (t • A)‖ ≤ t * ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by
  set φ : ℝ → 𝔸 := fun σ => exp (σ • A) * B * exp ((t - σ) • A) with hφ
  have hderiv : ∀ σ : ℝ,
      HasDerivAt φ (exp (σ • A) * (A * B - B * A) * exp ((t - σ) • A)) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ : ℝ => exp (σ • A) * B) (exp (σ • A) * A * B) σ :=
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) A σ).mul_const B
    have h3 := h1.mul (hasDerivAt_exp_const_sub_smul A t σ)
    convert h3 using 1
    · rfl
    · noncomm_ring
  have hbound : ∀ σ ∈ Ico (0 : ℝ) t,
      ‖exp (σ • A) * (A * B - B * A) * exp ((t - σ) • A)‖
        ≤ ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by
    intro σ hσ
    have hσ0 : 0 ≤ σ := hσ.1
    have hσt : 0 ≤ t - σ := by linarith [hσ.2]
    calc ‖exp (σ • A) * (A * B - B * A) * exp ((t - σ) • A)‖
        ≤ ‖exp (σ • A)‖ * ‖A * B - B * A‖ * ‖exp ((t - σ) • A)‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ Real.exp (σ * ‖A‖) * ‖A * B - B * A‖ * Real.exp ((t - σ) * ‖A‖) := by
          gcongr
          · exact norm_exp_smul_le A hσ0
          · exact norm_exp_smul_le A hσt
      _ = ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by
          rw [mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add]
          ring_nf
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x _ => (hderiv x).hasDerivWithinAt) hbound t ⟨ht, le_rfl⟩
  have hφt : φ t = exp (t • A) * B := by simp [hφ]
  have hφ0 : φ 0 = B * exp (t • A) := by simp [hφ]
  rw [hφt, hφ0, sub_zero] at hmvt
  calc ‖exp (t • A) * B - B * exp (t • A)‖
      ≤ ‖A * B - B * A‖ * Real.exp (t * ‖A‖) * t := hmvt
    _ = t * ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by ring
end LieTrotter
