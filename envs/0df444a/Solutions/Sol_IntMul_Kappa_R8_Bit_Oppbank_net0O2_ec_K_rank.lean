-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ec_K_rank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:53:19.309393+00:00
-- url     : https://prove2.me/submissions/5acefc60-60e9-45f7-85ca-3b34e36d2b28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pnd_Pl_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_rank_mul_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pl_rank_one
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a s : ℕ) (ha : a < v) (hs : s < v) :
    (K S0 Si0 (Pl a) (Pl s)).rank = 1 := by
  have hFB := FB0_S0_Si0
  have h := K_rank_mul_idem S0 Si0 hFB.1 hFB.2.1 (Pl a) (Pl s)
    (Pnd_Pl_idem ha) (Pnd_Pl_idem hs)
  rw [h, Pl_rank_one ha, Pl_rank_one hs]
