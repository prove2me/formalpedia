-- Prove2me | solution 1 for KobayashiMaskawa1973.mem_unitaryGroup_three_of_star_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:23:44.953229+00:00
-- url     : https://prove2.me/submissions/bebf8b39-7450-48c2-89a4-f5d6f1619936

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix
open KobayashiMaskawa1973

theorem solution (U : Matrix (Fin 3) (Fin 3) ℂ) (h : star U * U = 1) :
    U ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact h
