-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_e2_K_rank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:54:45.582482+00:00
-- url     : https://prove2.me/submissions/7d4164b6-c1ae-420f-8ca9-ddf89d87c4fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pnd_Pl_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_pos
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_rank_mul_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_rank_eq_rkC
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pl_rank_one
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a o c : ℕ) (ha : a < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    (K S0 Si0 (Pl a) (Dm o c)).rank = rkC o c := by
  have hFB := FB0_S0_Si0
  have h := K_rank_mul_idem S0 Si0 hFB.1 hFB.2.1 (Pl a) (Dm o c)
    (Pnd_Pl_idem ha) (Dm_idem_pos o c ho hc hr)
  rw [h, Pl_rank_one ha, Dm_rank_eq_rkC ho hc hr, one_mul]
