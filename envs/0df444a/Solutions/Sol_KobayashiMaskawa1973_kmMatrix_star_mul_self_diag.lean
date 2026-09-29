-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_star_mul_self_diag
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:48:20.586477+00:00
-- url     : https://prove2.me/submissions/c24ccfb1-9c52-4edf-8fa2-5adab4d0438b

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_00
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_11
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_22

open Matrix
open KobayashiMaskawa1973

theorem solution (θ₁ θ₂ θ₃ δ : ℝ) (i : Fin 3) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i i = 1 := by
  fin_cases i
  · exact kmMatrix_star_mul_self_00 θ₁ θ₂ θ₃ δ
  · exact kmMatrix_star_mul_self_11 θ₁ θ₂ θ₃ δ
  · exact kmMatrix_star_mul_self_22 θ₁ θ₂ θ₃ δ
