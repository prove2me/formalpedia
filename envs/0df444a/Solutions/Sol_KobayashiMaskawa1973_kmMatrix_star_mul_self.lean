-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_star_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:30:52.959971+00:00
-- url     : https://prove2.me/submissions/f800fd29-952c-4bab-9dc6-6764f804b11d

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_entries

open Matrix
open KobayashiMaskawa1973

theorem solution (θ₁ θ₂ θ₃ δ : ℝ) :
    star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ = 1 := by
  ext i j
  exact kmMatrix_star_mul_self_entries θ₁ θ₂ θ₃ δ i j
