-- Prove2me | solution 2 for KobayashiMaskawa1973.exists_unitary_three_not_rephasable_real
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T02:24:37.413119+00:00
-- url     : https://prove2.me/submissions/72acc7d7-c7d7-44ce-b19a-ea608be0a67f

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
theorem solution :
    ∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      ∀ V : Matrix (Fin 3) (Fin 3) ℂ, RephasingEquiv U V → ¬ IsRealMatrix V := by
  exact kmx_exists
