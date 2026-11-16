-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_cs1_locals_lt_NL_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:06:05.406262+00:00
-- url     : https://prove2.me/submissions/811a6403-a109-4d5e-8875-b37de483f990

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_genF_locals_of_W_rec
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_W1F_wires_lt_NL_rec
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.Gen (codeOf SG1_0)
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (ℓ : ℕ)
    (hℓ : ∃ ch ∈ cs1,
      (∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) :
    ℓ < NL := by
  unfold cs1 at hℓ
  exact net0O2_W1F_wires_lt_NL_rec ℓ (net0O2_genF_locals_of_W_rec (codeOf SG1_0) W1F ℓ hℓ)
