-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND_NDpt
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T11:09:26.199305+00:00
-- url     : https://prove2.me/submissions/2babd981-8208-4155-b8ad-5d9f6e1104da

-- NDpt helper pack (published Pnd only; no PndFix).
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptBits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptCard
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptPrj
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.NDptBits
open IntMul.Kappa.R8.Bit.Oppbank.NDptCard
open IntMul.Kappa.R8.Bit.Oppbank.NDptPrj

theorem solution :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      isND o = true → isPT c = true → dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
  intro o c ho hc hnest hNDo hPTc _hdim
  have ⟨ho_ge, _⟩ : 1773 ≤ o ∧ o < codeBound := by
    simp only [isND, Bool.and_eq_true] at hNDo
    exact ⟨Nat.ble_eq.mp hNDo.1, Nat.blt_eq.mp hNDo.2⟩
  have ⟨hc_ge, hc_lt⟩ : 2 ≤ c ∧ c < 1773 := by
    simp only [isPT, Bool.and_eq_true] at hPTc
    exact ⟨Nat.ble_eq.mp hPTc.1, Nat.blt_eq.mp hPTc.2⟩
  set ao := o - 1773
  set T := c - 2
  have hao : ao < nNodes := by
    have : codeBound = 64251 := rfl
    have : nNodes = 62478 := rfl
    omega
  have hT : T < 1771 := by omega
  have hCao := AllDensCentred ao hao
  have hoble : Nat.ble o 1 = false :=
    Bool.eq_false_iff.2 fun h => (by omega : ¬ o ≤ 1) (Nat.ble_eq.mp h)
  have hcble : Nat.ble c 1 = false :=
    Bool.eq_false_iff.2 fun h => (by omega : ¬ c ≤ 1) (Nat.ble_eq.mp h)
  have hNDc : isND c = false := by
    cases h : isND c
    · rfl
    · have ⟨hge, _⟩ : 1773 ≤ c ∧ c < codeBound := by
        simp only [isND, Bool.and_eq_true] at h
        exact ⟨Nat.ble_eq.mp h.1, Nat.blt_eq.mp h.2⟩
      omega
  have hPT_o : isPT o = false := by
    cases h : isPT o
    · rfl
    · have hlt : o < 1773 := by
        simp only [isPT, Bool.and_eq_true] at h; exact Nat.blt_eq.mp h.2
      omega
  have hor : orthOK ao T = true := by
    simp only [nestOK, hoble, hcble, hNDo, hNDc, hPT_o, hPTc, Bool.false_or, Bool.or_false,
      Bool.and_true, Bool.and_false, Bool.false_and, Bool.or_eq_true, Bool.and_eq_true] at hnest
    simpa [ao, T] using hnest
  have eo : o = 1773 + ao := by omega
  have ec : c = 2 + T := by omega
  have hPo : Pc o = Pnd (densSupG ao) := by
    rw [eo, Pc_of_ND ao (by omega), PndD]
  have hPc' : Pc c = 1 - Pl T := by
    simp [Pc, show c ≠ 0 by omega, show c ≠ 1 by omega, show c < 1773 by omega, T]
  have horth := orthOK_sound hT hor
  have hLe := Pnd_orth hCao hT horth
  simpa [hPo, hPc'] using hLe
