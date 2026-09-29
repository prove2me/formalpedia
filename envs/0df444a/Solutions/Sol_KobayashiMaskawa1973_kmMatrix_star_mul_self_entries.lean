-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_star_mul_self_entries
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:44:06.230531+00:00
-- url     : https://prove2.me/submissions/6ee110a9-8c81-4972-bbb6-f8241bce0dfe

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_diag
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_offdiag

open Matrix
open KobayashiMaskawa1973

theorem solution (θ₁ θ₂ θ₃ δ : ℝ) (i j : Fin 3) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq]
    exact kmMatrix_star_mul_self_diag θ₁ θ₂ θ₃ δ i
  · rw [Matrix.one_apply_ne h]
    exact kmMatrix_star_mul_self_offdiag θ₁ θ₂ θ₃ δ i j h
