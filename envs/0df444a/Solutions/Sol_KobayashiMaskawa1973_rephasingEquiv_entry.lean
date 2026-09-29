-- Prove2me | solution 1 for KobayashiMaskawa1973.rephasingEquiv_entry
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:45:39.359012+00:00
-- url     : https://prove2.me/submissions/44d34917-1748-48d1-be4e-a4cabe52148d

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix
open KobayashiMaskawa1973

theorem solution (U V : Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3 → ℝ)
    (h : phaseDiag a * U * phaseDiag b = V) (i j : Fin 3) :
    V i j = Complex.exp ((a i : ℂ) * Complex.I) * U i j * Complex.exp ((b j : ℂ) * Complex.I) := by
  rw [← h]
  simp [phaseDiag, mul_assoc]
