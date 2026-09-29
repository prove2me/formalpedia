-- Prove2me | solution 2 for KobayashiMaskawa1973.kmMatrix_not_rephasable_real_witness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T02:23:16.454059+00:00
-- url     : https://prove2.me/submissions/3b38ff55-cdff-4416-b89d-c4236b18a91e

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
theorem kmx_hE (δ : ℝ) :
    Complex.exp ((δ : ℂ) * Complex.I) * star (Complex.exp ((δ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

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
theorem solution :
    ∀ V : Matrix (Fin 3) (Fin 3) ℂ,
      RephasingEquiv (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)) V →
      ¬ IsRealMatrix V := by
  exact kmx_not_real
