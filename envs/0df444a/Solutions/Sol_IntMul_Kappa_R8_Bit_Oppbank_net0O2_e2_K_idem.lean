-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_e2_K_idem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:34:19.063521+00:00
-- url     : https://prove2.me/submissions/1c005067-7bba-4758-b80c-c7ef61e3a74b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pnd_Pl_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_pos
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.KAlgebra
open Matrix

theorem solution (a o c : ℕ) (ha : a < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    K S0 Si0 (Pl a) (Dm o c) * K S0 Si0 (Pl a) (Dm o c) = K S0 Si0 (Pl a) (Dm o c) := by
  have hFB := FB0_S0_Si0
  have hS : S0 * Si0 = 1 := hFB.1
  have hSi : Si0 * S0 = 1 := hFB.2.1
  exact K_idem S0 Si0 hS hSi (Pl a) (Dm o c) (Pnd_Pl_idem ha) (Dm_idem_pos o c ho hc hr)
