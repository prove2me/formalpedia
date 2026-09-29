-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_star_mul_self_00
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:34:56.969945+00:00
-- url     : https://prove2.me/submissions/e0ff82b8-7033-4269-967d-08c16bee3b2f

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open KobayashiMaskawa1973 Matrix in
theorem kmx_00 (θ₁ θ₂ θ₃ δ : ℝ) : kmMatrix θ₁ θ₂ θ₃ δ 0 0 = (Real.cos θ₁ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_01 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 0 1 = -(Real.sin θ₁ : ℂ) * (Real.cos θ₃ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_02 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 0 2 = -(Real.sin θ₁ : ℂ) * (Real.sin θ₃ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_10 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 1 0 = (Real.sin θ₁ : ℂ) * (Real.cos θ₂ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_11 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 1 1 = (Real.cos θ₁ : ℂ) * (Real.cos θ₂ : ℂ) * (Real.cos θ₃ : ℂ)
      - (Real.sin θ₂ : ℂ) * (Real.sin θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_12 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 1 2 = (Real.cos θ₁ : ℂ) * (Real.cos θ₂ : ℂ) * (Real.sin θ₃ : ℂ)
      + (Real.sin θ₂ : ℂ) * (Real.cos θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_20 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 2 0 = (Real.sin θ₁ : ℂ) * (Real.sin θ₂ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_21 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 2 1 = (Real.cos θ₁ : ℂ) * (Real.sin θ₂ : ℂ) * (Real.cos θ₃ : ℂ)
      + (Real.cos θ₂ : ℂ) * (Real.sin θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_22 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 2 2 = (Real.cos θ₁ : ℂ) * (Real.sin θ₂ : ℂ) * (Real.sin θ₃ : ℂ)
      - (Real.cos θ₂ : ℂ) * (Real.cos θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_star_real (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x

open KobayashiMaskawa1973 Matrix in
theorem kmx_hE (δ : ℝ) :
    Complex.exp ((δ : ℂ) * Complex.I) * star (Complex.exp ((δ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

open KobayashiMaskawa1973 Matrix in
theorem kmx_pyth (x : ℝ) : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.sin_sq_add_cos_sq x

open KobayashiMaskawa1973 Matrix in
theorem kmx_sms_00 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 0 0 = 1 := by
  have h1 := kmx_pyth θ₁
  have h2 := kmx_pyth θ₂
  have h3 := kmx_pyth θ₃
  have hE := kmx_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, kmx_00, kmx_01, kmx_02,
    kmx_10, kmx_11, kmx_12, kmx_20, kmx_21, kmx_22, star_sub, star_add, star_neg, star_mul',
    kmx_star_real]
  generalize star (Complex.exp ((δ : ℂ) * Complex.I)) = f at hE ⊢
  generalize Complex.exp ((δ : ℂ) * Complex.I) = e at hE ⊢
  generalize (Real.cos θ₁ : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ₁ : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ₂ : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ₂ : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ₃ : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ₃ : ℂ) = s3 at h3 ⊢
  linear_combination (1) * h1 + (s1^2) * h2

open KobayashiMaskawa1973 Matrix in
theorem solution (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 0 0 = 1 := by
  exact kmx_sms_00 θ₁ θ₂ θ₃ δ
