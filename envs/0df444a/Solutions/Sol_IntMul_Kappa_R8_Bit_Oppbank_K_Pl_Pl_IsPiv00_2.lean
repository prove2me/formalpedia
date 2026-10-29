-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.K_Pl_Pl_IsPiv00
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:58:08.890694+00:00
-- url     : https://prove2.me/submissions/8454eace-faac-403f-ab7a-d8b9efcea95d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_IsPiv_00_of_K_Pl_Pl
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
    IsPiv (K S Si (Pl a) (Pl s)) 0 0 :=
  IsPiv_00_of_K_Pl_Pl S Si hFB.1 hFB.2.1 ha hs
