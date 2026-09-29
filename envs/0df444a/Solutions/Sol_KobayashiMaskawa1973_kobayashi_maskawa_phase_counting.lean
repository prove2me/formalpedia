-- Prove2me | solution 1 for KobayashiMaskawa1973.kobayashi_maskawa_phase_counting
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T08:17:52.539158+00:00
-- url     : https://prove2.me/submissions/b34f2619-0ab9-41c2-8f16-247dbb9c9285

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
theorem kmx_cos4 : Real.cos (Real.pi / 4) = 1 / Real.sqrt 2 := by
  rw [Real.cos_pi_div_four]; exact Real.sqrt_div_self'

open KobayashiMaskawa1973 Matrix in
theorem kmx_sin4 : Real.sin (Real.pi / 4) = 1 / Real.sqrt 2 := by
  rw [Real.sin_pi_div_four]; exact Real.sqrt_div_self'

open KobayashiMaskawa1973 Matrix in
theorem kmx_expI : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  push_cast; exact Complex.exp_pi_div_two_mul_I

open KobayashiMaskawa1973 Matrix in
theorem kmx_sq2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

open KobayashiMaskawa1973 Matrix in
theorem kmx_sq2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (by positivity : Real.sqrt 2 ≠ 0)

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
theorem kmx_w00 :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0 = (1 / Real.sqrt 2 : ℂ) := by
  rw [kmx_00, kmx_cos4]; push_cast; rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_w01 :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1 = -1/2 := by
  rw [kmx_01, kmx_cos4, kmx_sin4]
  have hx := kmx_sq2
  have hx0 := kmx_sq2_ne
  push_cast
  generalize ((Real.sqrt 2 : ℝ) : ℂ) = x at hx hx0 ⊢
  field_simp
  linear_combination hx

open KobayashiMaskawa1973 Matrix in
theorem kmx_w10 :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0 = 1/2 := by
  rw [kmx_10, kmx_cos4, kmx_sin4]
  have hx := kmx_sq2
  have hx0 := kmx_sq2_ne
  push_cast
  generalize ((Real.sqrt 2 : ℝ) : ℂ) = x at hx hx0 ⊢
  field_simp
  linear_combination (-1) * hx

open KobayashiMaskawa1973 Matrix in
theorem kmx_w11 :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1 =
      (1 / (2 * Real.sqrt 2) - Complex.I / 2) := by
  rw [kmx_11, kmx_cos4, kmx_sin4, kmx_expI]
  have hx := kmx_sq2
  have hx0 := kmx_sq2_ne
  push_cast
  generalize ((Real.sqrt 2 : ℝ) : ℂ) = x at hx hx0 ⊢
  field_simp
  linear_combination (-(1 - x * Complex.I)) * hx

open KobayashiMaskawa1973 Matrix in
theorem kmx_star_half : star (1 / 2 : ℂ) = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, kmx_star_real]

open KobayashiMaskawa1973 Matrix in
theorem kmx_star_neg_half : star (-1 / 2 : ℂ) = -1 / 2 := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, kmx_star_real]

open KobayashiMaskawa1973 Matrix in
theorem kmx_quartet_im :
    ((kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0) *
     (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0)).im =
      1 / (8 * Real.sqrt 2) := by
  rw [kmx_w00, kmx_w11, kmx_w01, kmx_w10, kmx_star_half, kmx_star_neg_half]
  have key : (1 / ((Real.sqrt 2 : ℝ) : ℂ)) * (1 / (2 * ((Real.sqrt 2 : ℝ) : ℂ)) - Complex.I / 2) *
      (-1 / 2) * (1 / 2) =
      (((-1 / 16 : ℝ)) : ℂ) + ((1 / (8 * Real.sqrt 2) : ℝ) : ℂ) * Complex.I := by
    have hx := kmx_sq2
    have hx0 := kmx_sq2_ne
    push_cast
    generalize ((Real.sqrt 2 : ℝ) : ℂ) = x at hx hx0 ⊢
    field_simp
    linear_combination 64 * hx
  rw [key]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  ring

open KobayashiMaskawa1973 Matrix in
theorem kmx_quartet_ne :
    ((kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0) *
     (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0)).im ≠ 0 := by
  rw [kmx_quartet_im]; positivity

open KobayashiMaskawa1973 Matrix in
theorem kmx_phase (u00 u11 u01 u10 : ℂ) (a0 a1 b0 b1 : ℝ) :
    (Complex.exp ((a0 : ℂ) * Complex.I) * u00 * Complex.exp ((b0 : ℂ) * Complex.I)) *
    (Complex.exp ((a1 : ℂ) * Complex.I) * u11 * Complex.exp ((b1 : ℂ) * Complex.I)) *
    star (Complex.exp ((a0 : ℂ) * Complex.I) * u01 * Complex.exp ((b1 : ℂ) * Complex.I)) *
    star (Complex.exp ((a1 : ℂ) * Complex.I) * u10 * Complex.exp ((b0 : ℂ) * Complex.I)) =
    u00 * u11 * star u01 * star u10 := by
  have hA := kmx_hE a0
  have hB := kmx_hE a1
  have hC := kmx_hE b0
  have hD := kmx_hE b1
  simp only [star_mul']
  generalize star u01 = v01
  generalize star u10 = v10
  generalize star (Complex.exp ((a0 : ℂ) * Complex.I)) = fa0 at hA ⊢
  generalize star (Complex.exp ((a1 : ℂ) * Complex.I)) = fa1 at hB ⊢
  generalize star (Complex.exp ((b0 : ℂ) * Complex.I)) = fb0 at hC ⊢
  generalize star (Complex.exp ((b1 : ℂ) * Complex.I)) = fb1 at hD ⊢
  generalize Complex.exp ((a0 : ℂ) * Complex.I) = ea0 at hA ⊢
  generalize Complex.exp ((a1 : ℂ) * Complex.I) = ea1 at hB ⊢
  generalize Complex.exp ((b0 : ℂ) * Complex.I) = eb0 at hC ⊢
  generalize Complex.exp ((b1 : ℂ) * Complex.I) = eb1 at hD ⊢
  linear_combination (u00 * u11 * v01 * v10) * (ea1 * fa1) * (eb0 * fb0) * (eb1 * fb1) * hA
    + (u00 * u11 * v01 * v10) * (eb0 * fb0) * (eb1 * fb1) * hB
    + (u00 * u11 * v01 * v10) * (eb1 * fb1) * hC
    + (u00 * u11 * v01 * v10) * hD

open KobayashiMaskawa1973 Matrix in
theorem kmx_rephase (U V : Matrix (Fin 3) (Fin 3) ℂ) (h : RephasingEquiv U V) :
    V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0) = U 0 0 * U 1 1 * star (U 0 1) * star (U 1 0) := by
  obtain ⟨a, b, rfl⟩ := h
  simp only [phaseDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact kmx_phase (U 0 0) (U 1 1) (U 0 1) (U 1 0) (a 0) (a 1) (b 0) (b 1)

open KobayashiMaskawa1973 Matrix in
theorem kmx_real_quartet (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : IsRealMatrix V) :
    (V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0)).im = 0 := by
  have h00 := hV 0 0
  have h11 := hV 1 1
  have h01 := hV 0 1
  have h10 := hV 1 0
  simp [Complex.mul_im, Complex.mul_re, Complex.star_def, h00, h11, h01, h10]

open KobayashiMaskawa1973 Matrix in
theorem kmx_not_real :
    ∀ V : Matrix (Fin 3) (Fin 3) ℂ,
      RephasingEquiv (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)) V →
      ¬ IsRealMatrix V := by
  intro V hV hR
  have h1 := kmx_rephase _ V hV
  have h2 := kmx_real_quartet V hR
  rw [h1] at h2
  exact kmx_quartet_ne h2

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
theorem kmx_sms (θ₁ θ₂ θ₃ δ : ℝ) :
    star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ = 1 := by
  ext i j; exact kmx_entries θ₁ θ₂ θ₃ δ i j

open KobayashiMaskawa1973 Matrix in
theorem kmx_exists :
    ∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      ∀ V : Matrix (Fin 3) (Fin 3) ℂ, RephasingEquiv U V → ¬ IsRealMatrix V := by
  refine ⟨kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2), ?_, kmx_not_real⟩
  rw [Matrix.mem_unitaryGroup_iff']
  exact kmx_sms _ _ _ _
open KobayashiMaskawa1973 Matrix in
theorem kmr_star_real (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x

open KobayashiMaskawa1973 Matrix in
theorem kmr_hE (δ : ℝ) :
    Complex.exp ((δ : ℂ) * Complex.I) * star (Complex.exp ((δ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

open KobayashiMaskawa1973 Matrix in
theorem kmr_pyth (x : ℝ) : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.sin_sq_add_cos_sq x

open KobayashiMaskawa1973 Matrix in
theorem kmr_polar (z : ℂ) :
    z * Complex.exp (((-(Complex.arg z) : ℝ) : ℂ) * Complex.I) = ((‖z‖ : ℝ) : ℂ) := by
  have h0 : (Complex.arg z : ℂ) * Complex.I + ((-(Complex.arg z) : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast; ring
  calc z * Complex.exp (((-(Complex.arg z) : ℝ) : ℂ) * Complex.I)
      = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) *
          Complex.exp (((-(Complex.arg z) : ℝ) : ℂ) * Complex.I) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
    _ = ((‖z‖ : ℝ) : ℂ) := by rw [mul_assoc, ← Complex.exp_add, h0, Complex.exp_zero, mul_one]

open KobayashiMaskawa1973 Matrix in
theorem kmr_cs (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) :
    Real.cos (Complex.arg ((u : ℂ) + (v : ℂ) * Complex.I)) = u ∧
    Real.sin (Complex.arg ((u : ℂ) + (v : ℂ) * Complex.I)) = v := by
  set z : ℂ := (u : ℂ) + (v : ℂ) * Complex.I with hz
  have hre : z.re = u := by simp [hz]
  have him : z.im = v := by simp [hz]
  have hn2 : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; linear_combination h
  have hn : ‖z‖ = 1 := by
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  rw [hn, one_mul] at hc hs
  exact ⟨hc.trans hre, hs.trans him⟩

open KobayashiMaskawa1973 Matrix in
theorem kmr_phase_mem (m : ℕ) (a : Fin m → ℝ) :
    phaseDiag a ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold phaseDiag
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext k
  exact kmr_hE (a k)

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab00 (θ : ℝ) : cabibboMatrix θ 0 0 = (Real.cos θ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab01 (θ : ℝ) : cabibboMatrix θ 0 1 = (Real.sin θ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab10 (θ : ℝ) : cabibboMatrix θ 1 0 = -(Real.sin θ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab11 (θ : ℝ) : cabibboMatrix θ 1 1 = (Real.cos θ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab_mem (θ : ℝ) : cabibboMatrix θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h := kmr_pyth θ
  have e00 : (star (cabibboMatrix θ) * cabibboMatrix θ) 0 0 = 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, kmr_cab00, kmr_cab01,
      kmr_cab10, kmr_cab11, star_neg, kmr_star_real]
    linear_combination h
  have e01 : (star (cabibboMatrix θ) * cabibboMatrix θ) 0 1 = 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, kmr_cab00, kmr_cab01,
      kmr_cab10, kmr_cab11, star_neg, kmr_star_real]
    ring
  have e10 : (star (cabibboMatrix θ) * cabibboMatrix θ) 1 0 = 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, kmr_cab00, kmr_cab01,
      kmr_cab10, kmr_cab11, star_neg, kmr_star_real]
    ring
  have e11 : (star (cabibboMatrix θ) * cabibboMatrix θ) 1 1 = 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, kmr_cab00, kmr_cab01,
      kmr_cab10, kmr_cab11, star_neg, kmr_star_real]
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

open KobayashiMaskawa1973 Matrix in
theorem kmr_two (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ θ : ℝ, RephasingEquiv U (cabibboMatrix θ) := by
  set a : Fin 2 → ℝ := fun i => -(Complex.arg (U i 0)) with ha
  set U1 := phaseDiag a * U with hU1
  have hU1m : U1 ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (kmr_phase_mem 2 a) hU
  have hc0 : ∀ i, U1 i 0 = ((‖U i 0‖ : ℝ) : ℂ) := by
    intro i
    simp only [hU1, phaseDiag, Matrix.diagonal_mul, ha]
    rw [mul_comm]
    exact kmr_polar _
  set x0 := ‖U 0 0‖ with hx0
  set x1 := ‖U 1 0‖ with hx1
  have hx : x0 ^ 2 + x1 ^ 2 = 1 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU1m) 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc0, kmr_star_real,
      Matrix.one_apply_eq] at h
    have : ((x0 ^ 2 + x1 ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination h
    exact_mod_cast this
  obtain ⟨hcos, hsin⟩ := kmr_cs x0 (-x1) (by linear_combination hx)
  set θ := Complex.arg ((x0 : ℂ) + ((-x1 : ℝ) : ℂ) * Complex.I) with hθ
  set A := cabibboMatrix θ with hA
  have hAm : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := kmr_cab_mem θ
  set W := star A * U1 with hW
  have hWm : W ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem hAm) hU1m
  have hW00 : W 0 0 = 1 := by
    simp only [hW, hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc0, kmr_cab00,
      kmr_cab01, kmr_cab10, kmr_cab11, star_neg, kmr_star_real, hcos, hsin]
    have : ((x0 ^ 2 + x1 ^ 2 : ℝ) : ℂ) = 1 := by rw [hx]; simp
    push_cast at this ⊢
    linear_combination this
  have hW10 : W 1 0 = 0 := by
    simp only [hW, hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc0, kmr_cab00,
      kmr_cab01, kmr_cab10, kmr_cab11, star_neg, kmr_star_real, hcos, hsin]
    push_cast
    ring
  have hW01 : W 0 1 = 0 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hWm) 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hW00, hW10] at h
    simp at h
    exact h
  set b : Fin 2 → ℝ := ![0, -(Complex.arg (W 1 1))] with hb
  set M := W * phaseDiag b with hM
  have hMm : M ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ hWm (kmr_phase_mem 2 b)
  have hM11 : M 1 1 = ((‖W 1 1‖ : ℝ) : ℂ) := by
    simp only [hM, phaseDiag, Matrix.mul_diagonal, hb]
    exact kmr_polar _
  have hM00 : M 0 0 = 1 := by
    simp [hM, phaseDiag, Matrix.mul_diagonal, hb, hW00]
  have hM01 : M 0 1 = 0 := by
    simp [hM, phaseDiag, Matrix.mul_diagonal, hb, hW01]
  have hM10 : M 1 0 = 0 := by
    simp [hM, phaseDiag, Matrix.mul_diagonal, hb, hW10]
  have hy : ‖W 1 1‖ = 1 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hMm) 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hM11, hM10,
      kmr_star_real, Matrix.one_apply_eq] at h
    have h2 : ((‖W 1 1‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; simpa [sq] using h
    have h3 : ‖W 1 1‖ ^ 2 = 1 := by exact_mod_cast h2
    have h0 : 0 ≤ ‖W 1 1‖ := norm_nonneg _
    nlinarith
  have hM1 : M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM00, hM01, hM10, hM11, hy]
  refine ⟨θ, a, b, ?_⟩
  have hAA : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hAm
  calc phaseDiag a * U * phaseDiag b = (A * star A) * U1 * phaseDiag b := by
        rw [hAA, one_mul]
    _ = A * M := by simp only [hM, hW, Matrix.mul_assoc]
    _ = cabibboMatrix θ := by rw [hM1, Matrix.mul_one]

open KobayashiMaskawa1973 Matrix in
theorem kmr_k00 (θ₁ θ₂ θ₃ δ : ℝ) : kmMatrix θ₁ θ₂ θ₃ δ 0 0 = (Real.cos θ₁ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_k01 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 0 1 = -(Real.sin θ₁ : ℂ) * (Real.cos θ₃ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_k02 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 0 2 = -(Real.sin θ₁ : ℂ) * (Real.sin θ₃ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_k10 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 1 0 = (Real.sin θ₁ : ℂ) * (Real.cos θ₂ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_k11 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 1 1 = (Real.cos θ₁ : ℂ) * (Real.cos θ₂ : ℂ) * (Real.cos θ₃ : ℂ)
      - (Real.sin θ₂ : ℂ) * (Real.sin θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_k12 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 1 2 = (Real.cos θ₁ : ℂ) * (Real.cos θ₂ : ℂ) * (Real.sin θ₃ : ℂ)
      + (Real.sin θ₂ : ℂ) * (Real.cos θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_k20 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 2 0 = (Real.sin θ₁ : ℂ) * (Real.sin θ₂ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_k21 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 2 1 = (Real.cos θ₁ : ℂ) * (Real.sin θ₂ : ℂ) * (Real.cos θ₃ : ℂ)
      + (Real.cos θ₂ : ℂ) * (Real.sin θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_k22 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 2 2 = (Real.cos θ₁ : ℂ) * (Real.sin θ₂ : ℂ) * (Real.sin θ₃ : ℂ)
      - (Real.cos θ₂ : ℂ) * (Real.cos θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_ext3 (P Q : Matrix (Fin 3) (Fin 3) ℂ)
    (h00 : P 0 0 = Q 0 0) (h01 : P 0 1 = Q 0 1) (h02 : P 0 2 = Q 0 2)
    (h10 : P 1 0 = Q 1 0) (h11 : P 1 1 = Q 1 1) (h12 : P 1 2 = Q 1 2)
    (h20 : P 2 0 = Q 2 0) (h21 : P 2 1 = Q 2 1) (h22 : P 2 2 = Q 2 2) : P = Q := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

open KobayashiMaskawa1973 Matrix in
theorem kmr_A_unit (A : Matrix (Fin 3) (Fin 3) ℂ) (c1 s1 c2 s2 : ℝ)
    (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (e00 : A 0 0 = (c1 : ℂ)) (e01 : A 0 1 = -(s1 : ℂ)) (e02 : A 0 2 = 0)
    (e10 : A 1 0 = (s1 : ℂ) * (c2 : ℂ)) (e11 : A 1 1 = (c1 : ℂ) * (c2 : ℂ))
    (e12 : A 1 2 = -(s2 : ℂ))
    (e20 : A 2 0 = (s1 : ℂ) * (s2 : ℂ)) (e21 : A 2 1 = (c1 : ℂ) * (s2 : ℂ))
    (e22 : A 2 2 = (c2 : ℂ)) :
    A ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h1' : (c1 : ℂ) ^ 2 + (s1 : ℂ) ^ 2 = 1 := by exact_mod_cast h1
  have h2' : (c2 : ℂ) ^ 2 + (s2 : ℂ) ^ 2 = 1 := by exact_mod_cast h2
  apply kmr_ext3 <;>
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, e00, e01, e02, e10, e11,
    e12, e20, e21, e22, star_neg, star_mul', star_zero, kmr_star_real, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, Fin.reduceEq, not_false_eq_true] <;>
  first
    | ring1
    | linear_combination h2'
    | linear_combination h1' + (s1 : ℂ) ^ 2 * h2'
    | linear_combination h1' + (c1 : ℂ) ^ 2 * h2'
    | linear_combination (s1 : ℂ) * (c1 : ℂ) * h2'

open KobayashiMaskawa1973 Matrix in
theorem kmr_three (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    ∃ θ₁ θ₂ θ₃ δ : ℝ, RephasingEquiv U (kmMatrix θ₁ θ₂ θ₃ δ) := by
  set a : Fin 3 → ℝ := fun i => -(Complex.arg (U i 0)) with ha
  set U1 := phaseDiag a * U with hU1
  have hU1m : U1 ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
    Submonoid.mul_mem _ (kmr_phase_mem 3 a) hU
  have hc0 : ∀ i, U1 i 0 = ((‖U i 0‖ : ℝ) : ℂ) := by
    intro i
    simp only [hU1, phaseDiag, Matrix.diagonal_mul, ha]
    rw [mul_comm]
    exact kmr_polar _
  set x0 := ‖U 0 0‖ with hx0
  set x1 := ‖U 1 0‖ with hx1
  set x2 := ‖U 2 0‖ with hx2
  have hU10 : U1 0 0 = (x0 : ℂ) := hc0 0
  have hU11 : U1 1 0 = (x1 : ℂ) := hc0 1
  have hU12 : U1 2 0 = (x2 : ℂ) := hc0 2
  have hx : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 = 1 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU1m) 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hU10, hU11, hU12,
      kmr_star_real, Matrix.one_apply_eq] at h
    have : ((x0 ^ 2 + x1 ^ 2 + x2 ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination h
    exact_mod_cast this
  set z : ℂ := (x1 : ℂ) + (x2 : ℂ) * Complex.I with hz
  have hzre : z.re = x1 := by simp [hz]
  have hzim : z.im = x2 := by simp [hz]
  have hrc : ‖z‖ * Real.cos (Complex.arg z) = x1 := by rw [Complex.norm_mul_cos_arg, hzre]
  have hrs : ‖z‖ * Real.sin (Complex.arg z) = x2 := by rw [Complex.norm_mul_sin_arg, hzim]
  have hr2 : ‖z‖ ^ 2 = x1 ^ 2 + x2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]; ring
  obtain ⟨hcos1, hsin1⟩ := kmr_cs x0 ‖z‖ (by rw [hr2]; linear_combination hx)
  set θ₁ := Complex.arg ((x0 : ℂ) + ((‖z‖ : ℝ) : ℂ) * Complex.I) with hθ₁
  set θ₂ := Complex.arg z with hθ₂
  have hr1 : Real.sin θ₁ * Real.cos θ₂ = x1 := by rw [hsin1]; exact hrc
  have hr2' : Real.sin θ₁ * Real.sin θ₂ = x2 := by rw [hsin1]; exact hrs
  have hcos1' : ((Real.cos θ₁ : ℝ) : ℂ) = (x0 : ℂ) := by rw [hcos1]
  have hr1' : ((Real.sin θ₁ : ℝ) : ℂ) * ((Real.cos θ₂ : ℝ) : ℂ) = (x1 : ℂ) := by
    rw [← hr1]; push_cast; ring
  have hr2'' : ((Real.sin θ₁ : ℝ) : ℂ) * ((Real.sin θ₂ : ℝ) : ℂ) = (x2 : ℂ) := by
    rw [← hr2']; push_cast; ring
  have hcs2' : ((Real.cos θ₂ : ℝ) : ℂ) ^ 2 + ((Real.sin θ₂ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ₂
  have hx' : (x0 : ℂ) ^ 2 + (x1 : ℂ) ^ 2 + (x2 : ℂ) ^ 2 = 1 := by exact_mod_cast hx
  obtain ⟨A, e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ :
      ∃ A : Matrix (Fin 3) (Fin 3) ℂ,
        A 0 0 = ((Real.cos θ₁ : ℝ) : ℂ) ∧ A 0 1 = -((Real.sin θ₁ : ℝ) : ℂ) ∧ A 0 2 = 0 ∧
        A 1 0 = ((Real.sin θ₁ : ℝ) : ℂ) * ((Real.cos θ₂ : ℝ) : ℂ) ∧
        A 1 1 = ((Real.cos θ₁ : ℝ) : ℂ) * ((Real.cos θ₂ : ℝ) : ℂ) ∧
        A 1 2 = -((Real.sin θ₂ : ℝ) : ℂ) ∧
        A 2 0 = ((Real.sin θ₁ : ℝ) : ℂ) * ((Real.sin θ₂ : ℝ) : ℂ) ∧
        A 2 1 = ((Real.cos θ₁ : ℝ) : ℂ) * ((Real.sin θ₂ : ℝ) : ℂ) ∧
        A 2 2 = ((Real.cos θ₂ : ℝ) : ℂ) :=
    ⟨!![((Real.cos θ₁ : ℝ) : ℂ), -((Real.sin θ₁ : ℝ) : ℂ), 0;
        ((Real.sin θ₁ : ℝ) : ℂ) * ((Real.cos θ₂ : ℝ) : ℂ),
          ((Real.cos θ₁ : ℝ) : ℂ) * ((Real.cos θ₂ : ℝ) : ℂ), -((Real.sin θ₂ : ℝ) : ℂ);
        ((Real.sin θ₁ : ℝ) : ℂ) * ((Real.sin θ₂ : ℝ) : ℂ),
          ((Real.cos θ₁ : ℝ) : ℂ) * ((Real.sin θ₂ : ℝ) : ℂ), ((Real.cos θ₂ : ℝ) : ℂ)],
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hAm : A ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
    kmr_A_unit A _ _ _ _ (Real.cos_sq_add_sin_sq θ₁) (Real.cos_sq_add_sin_sq θ₂)
      e00 e01 e02 e10 e11 e12 e20 e21 e22
  set W := star A * U1 with hW
  have hWm : W ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem hAm) hU1m
  have hW00 : W 0 0 = 1 := by
    simp only [hW, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hU10, hU11, hU12,
      e00, e10, e20, star_mul', star_neg, star_zero, kmr_star_real]
    linear_combination (x0 : ℂ) * hcos1' + (x1 : ℂ) * hr1' + (x2 : ℂ) * hr2'' + hx'
  have hW10 : W 1 0 = 0 := by
    simp only [hW, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hU10, hU11, hU12,
      e01, e11, e21, star_mul', star_neg, star_zero, kmr_star_real]
    linear_combination ((Real.sin θ₁ : ℝ) : ℂ) * ((Real.cos θ₁ : ℝ) : ℂ) * hcs2'
      + ((Real.sin θ₁ : ℝ) : ℂ) * hcos1'
      - ((Real.cos θ₁ : ℝ) : ℂ) * ((Real.cos θ₂ : ℝ) : ℂ) * hr1'
      - ((Real.cos θ₁ : ℝ) : ℂ) * ((Real.sin θ₂ : ℝ) : ℂ) * hr2''
  have hW20 : W 2 0 = 0 := by
    simp only [hW, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hU10, hU11, hU12,
      e02, e12, e22, star_mul', star_neg, star_zero, kmr_star_real]
    linear_combination ((Real.sin θ₂ : ℝ) : ℂ) * hr1' - ((Real.cos θ₂ : ℝ) : ℂ) * hr2''
  have hWss := Matrix.mem_unitaryGroup_iff'.mp hWm
  have hW01 : W 0 1 = 0 := by
    have h := congrFun (congrFun hWss 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hW00, hW10, hW20] at h
    simp at h
    exact h
  have hW02 : W 0 2 = 0 := by
    have h := congrFun (congrFun hWss 2) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hW00, hW10, hW20] at h
    simp at h
    exact h
  set b : Fin 3 → ℝ := ![0, -(Complex.arg (W 1 1)), -(Complex.arg (W 1 2))] with hb
  set M := W * phaseDiag b with hM
  have hMm : M ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
    Submonoid.mul_mem _ hWm (kmr_phase_mem 3 b)
  have hMe : ∀ i j, M i j = W i j * Complex.exp ((b j : ℂ) * Complex.I) := by
    intro i j
    simp only [hM, phaseDiag, Matrix.mul_diagonal]
  have hb0 : b 0 = 0 := rfl
  have hM00 : M 0 0 = 1 := by rw [hMe, hW00, hb0]; simp
  have hM01 : M 0 1 = 0 := by rw [hMe, hW01, zero_mul]
  have hM02 : M 0 2 = 0 := by rw [hMe, hW02, zero_mul]
  have hM10 : M 1 0 = 0 := by rw [hMe, hW10, zero_mul]
  have hM20 : M 2 0 = 0 := by rw [hMe, hW20, zero_mul]
  have hM11 : M 1 1 = ((‖W 1 1‖ : ℝ) : ℂ) := by rw [hMe]; exact kmr_polar _
  have hM12 : M 1 2 = ((‖W 1 2‖ : ℝ) : ℂ) := by rw [hMe]; exact kmr_polar _
  have hMs := Matrix.mem_unitaryGroup_iff.mp hMm
  set y1 := ‖W 1 1‖ with hy1
  set y2 := ‖W 1 2‖ with hy2
  have hy : y1 ^ 2 + y2 ^ 2 = 1 := by
    have h := congrFun (congrFun hMs 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hM10, hM11, hM12,
      star_zero, mul_zero, zero_add, kmr_star_real, Matrix.one_apply_eq] at h
    have : ((y1 ^ 2 + y2 ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination h
    exact_mod_cast this
  have horth : M 2 1 * (y1 : ℂ) + M 2 2 * (y2 : ℂ) = 0 := by
    have h := congrFun (congrFun hMs 2) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hM10, hM11, hM12, hM20,
      star_zero, mul_zero, zero_add, kmr_star_real] at h
    rw [Matrix.one_apply_ne (by decide)] at h
    exact h
  have hunit : M 2 1 * star (M 2 1) + M 2 2 * star (M 2 2) = 1 := by
    have h := congrFun (congrFun hMs 2) 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, hM20, star_zero,
      mul_zero, zero_add, Matrix.one_apply_eq] at h
    exact h
  obtain ⟨hcos3, hsin3⟩ := kmr_cs y1 y2 hy
  set θ₃ := Complex.arg ((y1 : ℂ) + (y2 : ℂ) * Complex.I) with hθ₃
  have hy' : (y1 : ℂ) ^ 2 + (y2 : ℂ) ^ 2 = 1 := by exact_mod_cast hy
  obtain ⟨L, hL⟩ : ∃ L : ℂ, L = M 2 1 * (y2 : ℂ) - M 2 2 * (y1 : ℂ) := ⟨_, rfl⟩
  have hp : M 2 1 = L * (y2 : ℂ) := by
    rw [hL]; linear_combination (y1 : ℂ) * horth - M 2 1 * hy'
  have hq : M 2 2 = -(L * (y1 : ℂ)) := by
    rw [hL]; linear_combination (y2 : ℂ) * horth - M 2 2 * hy'
  have hLL : L * star L = 1 := by
    rw [hp, hq] at hunit
    simp only [star_mul', star_neg, kmr_star_real] at hunit
    linear_combination hunit - (L * star L) * hy'
  have hLn : ‖L‖ = 1 := by
    have h1 : ((‖L‖ ^ 2 : ℝ) : ℂ) = L * star L := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hLL] at h1
    have h2 : ‖L‖ ^ 2 = 1 := by exact_mod_cast h1
    have h0 : 0 ≤ ‖L‖ := norm_nonneg _
    nlinarith
  have hLe : Complex.exp ((Complex.arg L : ℂ) * Complex.I) = L := by
    have h := Complex.norm_mul_exp_arg_mul_I L
    rw [hLn, Complex.ofReal_one, one_mul] at h
    exact h
  set δ := Complex.arg L with hδ
  have hM11' : M 1 1 = ((Real.cos θ₃ : ℝ) : ℂ) := by rw [hM11, hcos3]
  have hM12' : M 1 2 = ((Real.sin θ₃ : ℝ) : ℂ) := by rw [hM12, hsin3]
  have hM21 : M 2 1 = ((Real.sin θ₃ : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := by
    rw [hp, hLe, hsin3]; ring
  have hM22 : M 2 2 = -((Real.cos θ₃ : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := by
    rw [hq, hLe, hcos3]; ring
  refine ⟨θ₁, θ₂, θ₃, δ, a, b, ?_⟩
  have hAA : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hAm
  have hfac : phaseDiag a * U * phaseDiag b = A * M := by
    calc phaseDiag a * U * phaseDiag b = (A * star A) * U1 * phaseDiag b := by
          rw [hAA, one_mul]
      _ = A * M := by simp only [hM, hW, Matrix.mul_assoc]
  rw [hfac]
  apply kmr_ext3 <;>
  simp only [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e02, e10, e11, e12, e20, e21, e22,
    hM00, hM01, hM02, hM10, hM20, hM11', hM12', hM21, hM22, kmr_k00, kmr_k01, kmr_k02, kmr_k10,
    kmr_k11, kmr_k12, kmr_k20, kmr_k21, kmr_k22] <;>
  ring

open KobayashiMaskawa1973 Matrix in
theorem solution :
    (∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ θ : ℝ, RephasingEquiv U (cabibboMatrix θ)) ∧
    (∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      ∀ V : Matrix (Fin 3) (Fin 3) ℂ, RephasingEquiv U V → ¬ IsRealMatrix V) ∧
    (∀ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      ∃ θ₁ θ₂ θ₃ δ : ℝ, RephasingEquiv U (kmMatrix θ₁ θ₂ θ₃ δ)) := by
  exact ⟨kmr_two, kmx_exists, kmr_three⟩
