-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.K_Dm_Pl_idem2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:24:51.082113+00:00
-- url     : https://prove2.me/submissions/36a20cca-ac70-4a2e-8df4-36cadb8e4466
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_of_nest
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)
open IntMul.Kappa.R8.Bit.Oppbank.KAlgebra
open IntMul.Kappa.R8.Bit.Oppbank.NetFB

theorem solution (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1)
    {b o c : ℕ} (hb : b < 1771) (ho : o < codeBound) (hc : c < codeBound)
    (hn : nestOK o c = true) :
    K S Si (Dm o c) (Pl b) * K S Si (Dm o c) (Pl b) = K S Si (Dm o c) (Pl b) :=
  K_idem S Si hS hSi (Dm o c) (Pl b) (Dm_idem_of_nest ho hc hn) (Pl_idem hb)
