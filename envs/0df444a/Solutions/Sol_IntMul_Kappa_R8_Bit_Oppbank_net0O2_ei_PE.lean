-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ei_PE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:12:17.226342+00:00
-- url     : https://prove2.me/submissions/a5e78620-ce56-4f04-ba41-ac719ed86f38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_ex
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mPl_one_rank_22
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mPl_one_IsPivs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.KAlgebra
open IntMul.Kappa.R8.Bit.Oppbank.NetFB

private theorem one_sub_Pl_idem {a : ℕ} (ha : a < 1771) :
    (1 - Pl a) * (1 - Pl a) = (1 - Pl a : M23) := by
  have hP : Pl a * Pl a = Pl a := Pl_idem ha
  rw [sub_mul, one_mul, mul_sub, mul_one, hP, sub_self, sub_zero]

private theorem one_idem : (1 : M23) * 1 = 1 := one_mul _

theorem solution (a : ℕ) (ha : a < v) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22) e := by
  have hFB : FB0 S0 Si0 := by
    have hex : ∃ S Sinv, FB0 S Sinv := FB0_ex
    have hS : ∃ Sinv, FB0 S0 Sinv :=
      Classical.epsilon_spec (p := fun S : Matrix (Fin 529) Pr23 ℚ => ∃ Sinv, FB0 S Sinv) hex
    exact Classical.epsilon_spec (p := fun Sinv : Matrix Pr23 (Fin 529) ℚ => FB0 S0 Sinv) hS
  have hS : S0 * Si0 = 1 := hFB.1
  have hSi : Si0 * S0 = 1 := hFB.2.1
  have hidem := K_idem S0 Si0 hS hSi (1 - Pl a) 1 (one_sub_Pl_idem ha) one_idem
  have hrank := K_mPl_one_rank_22 S0 Si0 hS hSi ha
  have hpiv := K_mPl_one_IsPivs S0 Si0 hFB ha
  exact oneRun_of_pivs 22 (by decide) (by decide) _ hidem hrank hpiv
