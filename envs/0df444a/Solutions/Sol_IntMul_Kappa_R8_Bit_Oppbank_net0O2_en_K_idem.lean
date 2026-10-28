-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_K_idem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:27:43.499239+00:00
-- url     : https://prove2.me/submissions/68daec6e-8d63-4f76-a829-a0572bb16928
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

theorem solution (a t : ℕ) (ha : a < v) (ht : t < v) :
    K S0 Si0 (1 - Pl a) (1 - Pl t) * K S0 Si0 (1 - Pl a) (1 - Pl t) =
      K S0 Si0 (1 - Pl a) (1 - Pl t) := by
  have hFB := FB0_S0_Si0
  have hS : S0 * Si0 = 1 := hFB.1
  have hSi : Si0 * S0 = 1 := hFB.2.1
  have hA : (1 - Pl a) * (1 - Pl a) = 1 - Pl a := one_sub_idem (Pnd_Pl_idem ha)
  have hB : (1 - Pl t) * (1 - Pl t) = 1 - Pl t := one_sub_idem (Pnd_Pl_idem ht)
  exact K_idem S0 Si0 hS hSi (1 - Pl a) (1 - Pl t) hA hB
