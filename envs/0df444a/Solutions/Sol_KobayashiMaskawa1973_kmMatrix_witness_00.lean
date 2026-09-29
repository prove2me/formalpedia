-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_witness_00
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:34:56.781746+00:00
-- url     : https://prove2.me/submissions/3fbdecc6-f7ad-4b0d-b2b7-22a783cf3654

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open KobayashiMaskawa1973 Matrix in
theorem kmx_00 (θ₁ θ₂ θ₃ δ : ℝ) : kmMatrix θ₁ θ₂ θ₃ δ 0 0 = (Real.cos θ₁ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmx_cos4 : Real.cos (Real.pi / 4) = 1 / Real.sqrt 2 := by
  rw [Real.cos_pi_div_four]; exact Real.sqrt_div_self'

open KobayashiMaskawa1973 Matrix in
theorem kmx_w00 :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0 = (1 / Real.sqrt 2 : ℂ) := by
  rw [kmx_00, kmx_cos4]; push_cast; rfl

open KobayashiMaskawa1973 Matrix in
theorem solution :
    kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0 = (1 / Real.sqrt 2 : ℂ) := by
  exact kmx_w00
