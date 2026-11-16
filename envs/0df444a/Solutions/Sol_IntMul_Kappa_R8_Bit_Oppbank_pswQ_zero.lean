-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.pswQ_zero
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:01:32.460293+00:00
-- url     : https://prove2.me/submissions/8320f60b-9833-489b-a7f3-38b08aa8d5ed

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R6.Bit.NB
open Matrix
theorem solution {m : ℕ} : pswQ (0 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  unfold pswQ
  rw [sub_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
