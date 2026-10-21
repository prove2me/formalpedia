-- Prove2me | solution 1 for IntMul.Kappa.R8.bitNetR8_mom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:25:38.271989+00:00
-- url     : https://prove2.me/submissions/c504eb41-1312-46cf-a073-ccb4cb46615c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_R8_bitNetR7plain_mom
import Theorems.Thm_IntMul_Kappa_R8_Bit_oppbank_mom_of_plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.R8 IntMul.Kappa.R8.Bit

/-- Round-eight bit moment network via opposite-bank recompile of the round-seven plain witness. -/
theorem solution : BitNetMomStmtG 104719230 529 Jain.bitR8 :=
  oppbank_mom_of_plain bitNetR7plain_mom
