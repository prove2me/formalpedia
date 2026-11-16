-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.move1_of_nest_ND_PT
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T11:12:48.650276+00:00
-- url     : https://prove2.me/submissions/940a006b-0130-44f4-bd85-9c03e67efca9

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_NDpt
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_of_Le_dim
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
    (hNDo : isND o = true) (hPTc : isPT c = true)
    (hdim : dimCF o < dimCF c) :
    pswQ (K S Si (Dm o c) (Pl b)) * Φ₁ S Si b o = Φ₁ S Si b c := by
  have hLe := nest_Le_ND_NDpt o c ho hc hok hNDo hPTc (le_of_lt hdim)
  have hle : dimCF o ≤ dimCF c := le_of_lt hdim
  exact move1_of_Le_dim S Si hSi ho hc hb (Or.inl ⟨hle, hLe⟩)
