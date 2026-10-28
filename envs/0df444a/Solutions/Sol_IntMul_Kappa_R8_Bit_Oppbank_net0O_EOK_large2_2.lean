-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O_EOK_large2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:29:42.17999+00:00
-- url     : https://prove2.me/submissions/391b7b2b-c9fc-4485-b8ba-654d0b761671
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOBasis
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_ex
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO_GoodM_large2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO_edgeMats_large2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank.EOKOBasis
open IntMul.Kappa.R8.Bit.Oppbank

/-!
Assemble `EOKOLargeStmt` from FB0_ex + GoodM_large2 + edgeMats_large2.
-/

theorem solution : EOKOLargeStmt := by
  obtain ⟨qG, hG⟩ := EOKO_GoodM_large2
  obtain ⟨qE, hE⟩ := EOKO_edgeMats_large2
  refine ⟨qG + qE, fun q hq hlt f => ?_⟩
  have hltG : qG < q := by omega
  have hltE : qE < q := by omega
  obtain ⟨hgS, hgSi, hgPc, hgPl⟩ := hG q hq hltG f
  obtain ⟨hm1, hm2, hmx, hmn, hmi, hmc⟩ := hE q hq hltE f
  exact {
    hS := ch0O_hS FB0_ex
    hSi := ch0O_hSi FB0_ex
    gS := hgS
    gSi := hgSi
    gPc := hgPc
    gPl := hgPl
    m1 := hm1
    m2 := hm2
    mx := hmx
    mn := hmn
    mi := hmi
    mc := hmc
  }
