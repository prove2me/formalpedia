-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.oppbank_mom_of_plain
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:31:47.287894+00:00
-- url     : https://prove2.me/submissions/60e2b192-de09-4b68-85dd-cb9d5ed95fa3
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
