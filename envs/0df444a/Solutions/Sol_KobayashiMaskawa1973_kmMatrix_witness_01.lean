-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_witness_01
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T02:16:17.774726+00:00
-- url     : https://prove2.me/submissions/012afa81-dda1-433e-8d0b-dc9f7e007503

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open KobayashiMaskawa1973 Matrix in
theorem kmx_01 (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ 0 1 = -(Real.sin θ₁ : ℂ) * (Real.cos θ₃ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_cos4 : Real.cos (Real.pi / 4) = 1 / Real.sqrt 2 := by
  rw [Real.cos_pi_div_four]; exact Real.sqrt_div_self'

open KobayashiMaskawa1973 Matrix in
theorem kmx_sin4 : Real.sin (Real.pi / 4) = 1 / Real.sqrt 2 := by
  rw [Real.sin_pi_div_four]; exact Real.sqrt_div_self'

open KobayashiMaskawa1973 Matrix in
theorem kmx_sq2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

open KobayashiMaskawa1973 Matrix in
theorem kmx_sq2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (by positivity : Real.sqrt 2 ≠ 0)

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
theorem solution :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1 = -1/2 := by
  exact kmx_w01
