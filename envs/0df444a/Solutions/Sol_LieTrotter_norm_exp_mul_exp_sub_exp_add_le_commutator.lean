-- Prove2me | solution 1 for LieTrotter.norm_exp_mul_exp_sub_exp_add_le_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:05:33.655493+00:00
-- url     : https://prove2.me/submissions/e382955b-5615-4b2b-8a6c-4b7ee39231cb

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator
public import Theorems.Thm_LieTrotter_norm_exp_smul_le
public import Theorems.Thm_P2M_LieTrotter_hasDerivAt_exp_const_sub_smul__0b920a441cd3
public import Theorems.Thm_LieTrotter_norm_exp_smul_mul_sub_le

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (A B : 𝔸) :
    ‖exp A * exp B - exp (A + B)‖ ≤ ‖A * B - B * A‖ / 2 * Real.exp (‖A‖ + ‖B‖) := by
  set c := ‖A * B - B * A‖ * Real.exp (‖A‖ + ‖B‖) with hc
  set H : ℝ → 𝔸 := fun τ => exp ((1 - τ) • (A + B)) * (exp (τ • A) * exp (τ • B)) with hH
  set H' : ℝ → 𝔸 := fun τ =>
    exp ((1 - τ) • (A + B)) * ((exp (τ • A) * B - B * exp (τ • A)) * exp (τ • B)) with hH'
  have hderiv : ∀ τ : ℝ, HasDerivAt H (H' τ) τ := by
    intro τ
    have hA := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A τ
    have hB := hasDerivAt_exp_smul_const' (𝕂 := ℝ) B τ
    have h := (hasDerivAt_exp_const_sub_smul' (A + B) 1 τ).mul (hA.mul hB)
    convert h using 1
    · rfl
    · simp only [hH', Pi.mul_apply]
      noncomm_ring
  have hbound : ∀ τ ∈ Ico (0 : ℝ) 1, ‖H' τ‖ ≤ c * τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := hτ.1
    have h1τ : 0 ≤ 1 - τ := by linarith [hτ.2]
    have hE : ‖exp ((1 - τ) • (A + B))‖ ≤ Real.exp ((1 - τ) * (‖A‖ + ‖B‖)) :=
      (norm_exp_smul_le (A + B) h1τ).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_add_le A B) h1τ))
    have hK := norm_exp_smul_mul_sub_le A B hτ0
    have hEB := norm_exp_smul_le B hτ0
    calc ‖H' τ‖
        ≤ ‖exp ((1 - τ) • (A + B))‖
            * (‖exp (τ • A) * B - B * exp (τ • A)‖ * ‖exp (τ • B)‖) := by
          simp only [hH']
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ Real.exp ((1 - τ) * (‖A‖ + ‖B‖))
            * ((τ * ‖A * B - B * A‖ * Real.exp (τ * ‖A‖)) * Real.exp (τ * ‖B‖)) := by
          gcongr
      _ = c * τ := by
          rw [hc]
          have : Real.exp ((1 - τ) * (‖A‖ + ‖B‖)) * (Real.exp (τ * ‖A‖) * Real.exp (τ * ‖B‖))
              = Real.exp (‖A‖ + ‖B‖) := by
            rw [← Real.exp_add, ← Real.exp_add]
            ring_nf
          calc Real.exp ((1 - τ) * (‖A‖ + ‖B‖))
                * ((τ * ‖A * B - B * A‖ * Real.exp (τ * ‖A‖)) * Real.exp (τ * ‖B‖))
              = τ * ‖A * B - B * A‖ * (Real.exp ((1 - τ) * (‖A‖ + ‖B‖))
                  * (Real.exp (τ * ‖A‖) * Real.exp (τ * ‖B‖))) := by ring
            _ = ‖A * B - B * A‖ * Real.exp (‖A‖ + ‖B‖) * τ := by rw [this]; ring
  -- fence `f τ = H τ − H 0` by `c τ² / 2`
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun τ => H τ - H 0) (f' := H') (a := 0) (b := 1)
    (B := fun τ => c * τ ^ 2 / 2) (B' := fun τ => c * τ)
    (fun x _ => ((hderiv x).sub_const (H 0)).continuousAt.continuousWithinAt)
    (fun x _ => ((hderiv x).sub_const (H 0)).hasDerivWithinAt)
    (by simp)
    (fun x => by
      have := ((hasDerivAt_pow 2 x).const_mul c).div_const 2
      convert this using 1 <;> first | rfl | (norm_num; try ring))
    hbound (x := 1) ⟨zero_le_one, le_rfl⟩
  have hH1 : H 1 = exp A * exp B := by simp [hH]
  have hH0 : H 0 = exp (A + B) := by simp [hH]
  simp only [hH1, hH0] at hfence
  calc ‖exp A * exp B - exp (A + B)‖ ≤ c * 1 ^ 2 / 2 := hfence
    _ = ‖A * B - B * A‖ / 2 * Real.exp (‖A‖ + ‖B‖) := by rw [hc]; ring
end LieTrotter
