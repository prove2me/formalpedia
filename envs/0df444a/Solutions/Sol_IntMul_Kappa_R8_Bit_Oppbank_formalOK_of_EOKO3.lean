-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.formalOK_of_EOKO3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:58:26.909992+00:00
-- url     : https://prove2.me/submissions/2270025b-2255-4757-ab02-45c9a3f20ed5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_formalOK_circuit_of_EOKO2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution : FormalOKOfEOKOStmt := fun N h => formalOK_circuit_of_EOKO2 N h
