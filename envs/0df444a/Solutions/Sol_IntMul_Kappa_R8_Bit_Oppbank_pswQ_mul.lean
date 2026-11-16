-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.pswQ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:30:51.839829+00:00
-- url     : https://prove2.me/submissions/dcc23eca-189e-48c6-8c02-830e99705f1b

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R6.Bit.NB
open Matrix
theorem solution {m : ℕ} (p p' : Matrix (Fin m) (Fin m) ℚ) :
    pswQ p * pswQ p' = pswQ (p + p' - 2 * (p * p')) := by
  unfold pswQ
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  congr 1 <;> noncomm_ring
