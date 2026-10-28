-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.K_Pl_Pl_IsPiv00
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:55:28.372152+00:00
-- url     : https://prove2.me/submissions/00f2fe8c-7631-42d4-b153-a1f4b2b2e7d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_Pl_Pl_rank_one
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_IsPiv_00_of_rank_one
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetFB

theorem solution (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hFB : FB0 S Si) {a s : ℕ} (ha : a < 1771) (hs : s < 1771) :
    IsPiv (K S Si (Pl a) (Pl s)) 0 0 := by
  have hS : S * Si = 1 := hFB.1
  have hSi : Si * S = 1 := hFB.2.1
  exact IsPiv_00_of_rank_one _ (K_Pl_Pl_rank_one S Si hS hSi ha hs)
