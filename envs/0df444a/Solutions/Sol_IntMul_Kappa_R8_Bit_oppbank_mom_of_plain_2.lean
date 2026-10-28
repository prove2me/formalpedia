-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.oppbank_mom_of_plain
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:48:31.386984+00:00
-- url     : https://prove2.me/submissions/8db712a3-e728-4ad9-876a-792b54b425d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_R6_Bit_BitNetMomStmtG_of_eq
import Theorems.Thm_IntMul_Kappa_R8_Bit_oppbank_net

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.R6.Bit IntMul.Kappa.R8.Bit

/-- Opposite-bank moment implication via the geometric network leaf and packaging. -/
theorem solution :
    BitNetMomStmtG 104719230 529 Jain.bitR7plain →
      BitNetMomStmtG 104719230 529 Jain.bitR8 := by
  intro _hplain
  obtain ⟨T, C, q₀, hRun, hOK, hmom⟩ := oppbank_net
  exact BitNetMomStmtG_of_eq 104719230 529 T q₀ Jain.bitR8 C hRun hOK hmom
