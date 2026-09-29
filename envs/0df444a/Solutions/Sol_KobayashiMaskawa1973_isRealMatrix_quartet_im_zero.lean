-- Prove2me | solution 1 for KobayashiMaskawa1973.isRealMatrix_quartet_im_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:25:50.766888+00:00
-- url     : https://prove2.me/submissions/9e57c21f-67f1-4c85-bcea-4f6cd5813b37

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix
open KobayashiMaskawa1973

theorem solution (V : Matrix (Fin 3) (Fin 3) ℂ) (h : IsRealMatrix V) :
    (V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0)).im = 0 := by
  have h00 := h 0 0
  have h11 := h 1 1
  have h01 := h 0 1
  have h10 := h 1 0
  first
  | simp [Complex.mul_im, Complex.im_conj, RCLike.conj_im, h00, h11, h01, h10]
  | simp [Complex.mul_im, h00, h11, h01, h10]
