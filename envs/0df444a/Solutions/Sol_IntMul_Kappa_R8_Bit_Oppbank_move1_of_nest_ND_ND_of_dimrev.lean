-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.move1_of_nest_ND_ND_of_dimrev
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T10:08:03.838421+00:00
-- url     : https://prove2.me/submissions/7bd21d09-1fa6-47e5-b9f9-5ba68e04725e

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nestOK_symm
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_ND_of_dim
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
    (hNDo : isND o = true) (hNDc : isND c = true)
    (hdim : dimCF c < dimCF o) :
    pswQ (K S Si (Dm o c) (Pl b)) * Φ₁ S Si b o = Φ₁ S Si b c := by
  have hok' : nestOK c o = true := by
    rw [← nestOK_symm o c]
    exact hok
  have hLe : Le (Pc c) (Pc o) :=
    nest_Le_ND_ND_of_dim c o hc ho hok' hNDc hNDo hdim
  have hnot : ¬ dimCF o ≤ dimCF c := not_le.mpr hdim
  exact move1_of_Le_dim S Si hSi ho hc hb (Or.inr ⟨hnot, hLe⟩)
