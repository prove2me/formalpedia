-- Prove2me | solution 2 for KobayashiMaskawa1973.kmMatrix_star_mul_self_entries
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:11:33.559261+00:00
-- url     : https://prove2.me/submissions/e7773f8c-5956-4ca9-a564-f1abd1723575

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
theorem kmx_sms_01 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 0 1 = 0 := by
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
  linear_combination (c1*s1*c3) * h2

open KobayashiMaskawa1973 Matrix in
theorem kmx_sms_02 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 0 2 = 0 := by
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
  linear_combination (c1*s1*s3) * h2

open KobayashiMaskawa1973 Matrix in
theorem kmx_sms_10 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 1 0 = 0 := by
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
  linear_combination (c1*s1*c3) * h2

open KobayashiMaskawa1973 Matrix in
theorem kmx_sms_11 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 1 1 = 1 := by
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
  linear_combination (s2^2*c3^2 + c2^2*c3^2) * h1 + (s3^2*e*f + c3^2 - s1^2*c3^2) * h2 + (1) * h3 + (s3^2) * hE

open KobayashiMaskawa1973 Matrix in
theorem kmx_sms_12 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 1 2 = 0 := by
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
  linear_combination (s2^2*c3*s3 + c2^2*c3*s3) * h1 + (c3*s3 - c3*s3*e*f - s1^2*c3*s3) * h2 + (-c3*s3) * hE

open KobayashiMaskawa1973 Matrix in
theorem kmx_sms_20 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 2 0 = 0 := by
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
  linear_combination (c1*s1*s3) * h2

open KobayashiMaskawa1973 Matrix in
theorem kmx_sms_21 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 2 1 = 0 := by
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
  linear_combination (s2^2*c3*s3 + c2^2*c3*s3) * h1 + (c3*s3 - c3*s3*e*f - s1^2*c3*s3) * h2 + (-c3*s3) * hE

open KobayashiMaskawa1973 Matrix in
theorem kmx_sms_22 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 2 2 = 1 := by
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
  linear_combination (s2^2*s3^2 + c2^2*s3^2) * h1 + (s3^2 + c3^2*e*f - s1^2*s3^2) * h2 + (e*f) * h3 + (1 - s3^2) * hE

open KobayashiMaskawa1973 Matrix in
theorem kmx_diag (θ₁ θ₂ θ₃ δ : ℝ) (i : Fin 3) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i i = 1 := by
  fin_cases i
  · exact kmx_sms_00 θ₁ θ₂ θ₃ δ
  · exact kmx_sms_11 θ₁ θ₂ θ₃ δ
  · exact kmx_sms_22 θ₁ θ₂ θ₃ δ

open KobayashiMaskawa1973 Matrix in
theorem kmx_offdiag (θ₁ θ₂ θ₃ δ : ℝ) (i j : Fin 3) (h : i ≠ j) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i j = 0 := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl h
    | exact kmx_sms_01 θ₁ θ₂ θ₃ δ
    | exact kmx_sms_02 θ₁ θ₂ θ₃ δ
    | exact kmx_sms_10 θ₁ θ₂ θ₃ δ
    | exact kmx_sms_12 θ₁ θ₂ θ₃ δ
    | exact kmx_sms_20 θ₁ θ₂ θ₃ δ
    | exact kmx_sms_21 θ₁ θ₂ θ₃ δ

open KobayashiMaskawa1973 Matrix in
theorem kmx_entries (θ₁ θ₂ θ₃ δ : ℝ) (i j : Fin 3) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact kmx_diag θ₁ θ₂ θ₃ δ i
  · rw [Matrix.one_apply_ne h]; exact kmx_offdiag θ₁ θ₂ θ₃ δ i j h

open KobayashiMaskawa1973 Matrix in
theorem solution (θ₁ θ₂ θ₃ δ : ℝ) (i j : Fin 3) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  exact kmx_entries θ₁ θ₂ θ₃ δ i j
