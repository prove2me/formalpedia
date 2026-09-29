-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:18:41.657636+00:00
-- url     : https://prove2.me/submissions/3ee2901b-3ac0-4bca-9822-09f346e96984

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self
import Theorems.Thm_KobayashiMaskawa1973_mem_unitaryGroup_three_of_star_mul_self

open Matrix
open KobayashiMaskawa1973

theorem solution (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  exact mem_unitaryGroup_three_of_star_mul_self (kmMatrix θ₁ θ₂ θ₃ δ) (kmMatrix_star_mul_self θ₁ θ₂ θ₃ δ)
