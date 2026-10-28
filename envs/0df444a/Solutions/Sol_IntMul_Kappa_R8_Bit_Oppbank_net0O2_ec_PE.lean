-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ec_PE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:05:50.839675+00:00
-- url     : https://prove2.me/submissions/9fe7b1d6-e764-4ce5-83d9-b423ea159b1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOBasis
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_ex
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_Pl_Pl_rank_one
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_Pl_Pl_IsPiv00
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.KAlgebra
open IntMul.Kappa.R8.Bit.Oppbank.EOKOBasis

theorem solution (a s : ℕ) (ha : a < v) (hs : s < v) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (Pl a) (Pl s)) (oneRun 1) e := by
  have hFB : FB0 S0 Si0 := by
    have hex : ∃ S Sinv, FB0 S Sinv := FB0_ex
    have hS : ∃ Sinv, FB0 S0 Sinv :=
      Classical.epsilon_spec (p := fun S : Matrix (Fin 529) Pr23 ℚ => ∃ Sinv, FB0 S Sinv) hex
    exact Classical.epsilon_spec (p := fun Sinv : Matrix Pr23 (Fin 529) ℚ => FB0 S0 Sinv) hS
  have hS : S0 * Si0 = 1 := hFB.1
  have hSi : Si0 * S0 = 1 := hFB.2.1
  have hidem := K_Pl_Pl_idem S0 Si0 hS hSi ha hs
  have hrank := K_Pl_Pl_rank_one S0 Si0 hS hSi ha hs
  have hpiv := K_Pl_Pl_IsPiv00 S0 Si0 hFB ha hs
  exact oneRun1_of_piv _ hidem hrank hpiv
