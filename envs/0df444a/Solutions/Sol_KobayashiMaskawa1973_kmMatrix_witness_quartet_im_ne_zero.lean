-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_witness_quartet_im_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:30:30.379733+00:00
-- url     : https://prove2.me/submissions/225dae12-94bd-4ad7-966b-26730c36b6cc

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_witness_quartet_im_eq
import Theorems.Thm_KobayashiMaskawa1973_one_div_eight_mul_sqrt_two_ne_zero

open Matrix
open KobayashiMaskawa1973

theorem solution :
    ((kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 0) *
     (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 0 1) *
     star (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) 1 0)).im ≠ 0 := by
  rw [kmMatrix_witness_quartet_im_eq]
  exact one_div_eight_mul_sqrt_two_ne_zero
