-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ei_K_idem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:27:42.943233+00:00
-- url     : https://prove2.me/submissions/a577bd09-c327-45ce-a0ac-47c6db8c4d60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pnd_Pl_idem
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.KAlgebra
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open Matrix

private theorem one_idem : (1 : M23) * 1 = 1 := by simp

theorem solution (a : ℕ) (ha : a < v) :
    K S0 Si0 (1 - Pl a) 1 * K S0 Si0 (1 - Pl a) 1 = K S0 Si0 (1 - Pl a) 1 := by
  have hFB := FB0_S0_Si0
  have hS : S0 * Si0 = 1 := hFB.1
  have hSi : Si0 * S0 = 1 := hFB.2.1
  have hA : (1 - Pl a) * (1 - Pl a) = 1 - Pl a := one_sub_idem (Pnd_Pl_idem ha)
  exact K_idem S0 Si0 hS hSi (1 - Pl a) (1 : M23) hA one_idem
