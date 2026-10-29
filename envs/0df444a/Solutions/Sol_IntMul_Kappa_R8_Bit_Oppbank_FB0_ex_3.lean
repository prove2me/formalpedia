-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.Oppbank.FB0_ex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:29:34.994212+00:00
-- url     : https://prove2.me/submissions/191c6139-0f2f-4037-b8b3-c14c8ecdf3e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_flagBasis
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_hPis0
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped Kronecker
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetFB
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution : ∃ S Sinv, FB0 S Sinv :=
  flagBasis Lab0 hLab0 Pis0 hPis0
