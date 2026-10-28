-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.EOKO2_oneRun_PE_families
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:57:22.484469+00:00
-- url     : https://prove2.me/submissions/d36b9927-dcd4-4b3e-8d87-b0c3282adcc3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_PE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e2_PE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_PE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_PE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ei_PE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_PE
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (Dm Pl nestOK K rkC S0 Si0)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2 (PE oneRun ch0O toNB)
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)

private theorem ch0NB_S : ch0NB.S = S0 := by
  simp only [ch0NB, toNB, ch0O]

private theorem ch0NB_Si : ch0NB.Si = Si0 := by
  simp only [ch0NB, toNB, ch0O]

theorem solution :
    (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
      ∃ e, PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c)) e) ∧
    (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
      ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c)) e) ∧
    (∀ b < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22) e) ∧
    (∀ a < 1771, ∀ t < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484) e) ∧
    (∀ a < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22) e) ∧
    (∀ a < 1771, ∀ s < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1) e) := by
  refine ⟨?h1, ?h2, ?hx, ?hn, ?hi, ?hc⟩
  · intro b hb o ho c hc _
    rw [ch0NB_S, ch0NB_Si]
    exact net0O2_e1_PE b o c hb ho hc
  · intro a ha o ho c hc _
    rw [ch0NB_S, ch0NB_Si]
    exact net0O2_e2_PE a o c ha ho hc
  · intro b hb
    rw [ch0NB_S, ch0NB_Si]
    exact net0O2_ex_PE b hb
  · intro a ha t ht
    rw [ch0NB_S, ch0NB_Si]
    exact net0O2_en_PE a t ha ht
  · intro a ha
    rw [ch0NB_S, ch0NB_Si]
    exact net0O2_ei_PE a ha
  · intro a ha s hs
    rw [ch0NB_S, ch0NB_Si]
    exact net0O2_ec_PE a s ha hs
