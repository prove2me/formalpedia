-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.move1_of_nest_ND_ND_of_dimne
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T10:10:31.501436+00:00
-- url     : https://prove2.me/submissions/96b896b9-664e-4bc5-85b1-27bafdfbb26f

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_of_nest_ND_ND_of_dim
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_of_nest_ND_ND_of_dimrev
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open Matrix

theorem solution
    (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {o c b : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hb : b < 1771)
    (hok : nestOK o c = true)
    (hNDo : isND o = true) (hNDc : isND c = true)
    (hdim : dimCF o < dimCF c ∨ dimCF c < dimCF o) :
    pswQ (K S Si (Dm o c) (Pl b)) * Φ₁ S Si b o = Φ₁ S Si b c := by
  rcases hdim with hfwd | hrev
  · exact move1_of_nest_ND_ND_of_dim S Si hSi ho hc hb hok hNDo hNDc hfwd
  · exact move1_of_nest_ND_ND_of_dimrev S Si hSi ho hc hb hok hNDo hNDc hrev
