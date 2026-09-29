-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_witness_entries
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:50:21.132462+00:00
-- url     : https://prove2.me/submissions/bebd9a11-af1a-4b19-a153-329af458a53b

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
theorem solution :
    (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0 = (1 / Real.sqrt 2 : ℂ)) ∧
    (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1 = -1/2) ∧
    (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0 = 1/2) ∧
    (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1 = (1 / (2 * Real.sqrt 2) - Complex.I / 2)) := by
  exact ⟨kmx_w00, kmx_w01, kmx_w10, kmx_w11⟩
