-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.IsPiv_00_of_rank_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:04:43.65221+00:00
-- url     : https://prove2.me/submissions/5c2b3d53-defb-4c23-b67e-6eed1366be17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_IsPiv_diag_of_rank
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (q : Matrix (Fin 529) (Fin 529) ℚ)
    (h : q.rank = 1) : IsPiv q 0 0 :=
  IsPiv_diag_of_rank q 1 h (by decide) 0 (by decide)
