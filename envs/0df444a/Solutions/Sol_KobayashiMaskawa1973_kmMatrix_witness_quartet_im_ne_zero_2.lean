-- Prove2me | solution 2 for KobayashiMaskawa1973.kmMatrix_witness_quartet_im_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:59:24.044329+00:00
-- url     : https://prove2.me/submissions/6b5df0a4-a82a-4251-aa5d-599f3dc2dbb9

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
theorem kmx_10 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 1 0 = (Real.sin θ₁ : ℂ) * (Real.cos θ₂ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_11 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 1 1 = (Real.cos θ₁ : ℂ) * (Real.cos θ₂ : ℂ) * (Real.cos θ₃ : ℂ)
      - (Real.sin θ₂ : ℂ) * (Real.sin θ₃ : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_star_real (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x

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
theorem solution :
    ((kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0) *
     (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0)).im ≠ 0 := by
  exact kmx_quartet_ne
