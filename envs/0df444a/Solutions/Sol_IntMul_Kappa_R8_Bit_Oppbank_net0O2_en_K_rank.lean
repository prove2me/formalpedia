-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_K_rank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:22:14.634365+00:00
-- url     : https://prove2.me/submissions/7007655d-0357-4875-8f31-954d24de67d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mPl_mPl_rank_484
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a t : ℕ) (ha : a < v) (ht : t < v) :
    (K S0 Si0 (1 - Pl a) (1 - Pl t)).rank = 484 := by
  have hFB := FB0_S0_Si0
  exact K_mPl_mPl_rank_484 S0 Si0 hFB.1 hFB.2.1 ha ht
