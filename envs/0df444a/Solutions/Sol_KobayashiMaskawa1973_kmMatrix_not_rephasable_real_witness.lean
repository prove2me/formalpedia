-- Prove2me | solution 1 for KobayashiMaskawa1973.kmMatrix_not_rephasable_real_witness
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:19:12.865023+00:00
-- url     : https://prove2.me/submissions/0b99930b-f09a-4fb5-af63-5e67d4542684

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs
import Theorems.Thm_KobayashiMaskawa1973_rephasingEquiv_quartet_invariant
import Theorems.Thm_KobayashiMaskawa1973_isRealMatrix_quartet_im_zero
import Theorems.Thm_KobayashiMaskawa1973_kmMatrix_witness_quartet_im_ne_zero

open Matrix
open KobayashiMaskawa1973

theorem solution (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : RephasingEquiv (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)) V) :
    ¬ IsRealMatrix V := by
  intro h_real
  have h_zero : (V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0)).im = 0 :=
    isRealMatrix_quartet_im_zero V h_real
  have h_eq := rephasingEquiv_quartet_invariant (kmMatrix (Real.pi / 4) (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)) V hV
  rw [h_eq] at h_zero
  exact kmMatrix_witness_quartet_im_ne_zero h_zero
