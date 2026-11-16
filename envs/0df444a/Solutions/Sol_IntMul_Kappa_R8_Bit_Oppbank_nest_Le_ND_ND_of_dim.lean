-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND_ND_of_dim
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:58:02.686946+00:00
-- url     : https://prove2.me/submissions/41b379d4-0b0d-49b2-a844-7d48b1e14bbe

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Le_Pnd_of_land
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel_of_dim
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_dimCF_of_ND
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_argRel_dim_le
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

theorem solution :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      isND o = true → isND c = true → dimCF o < dimCF c → Le (Pc o) (Pc c) := by
  intro o c ho hc hnest hNDo hNDc hdim
  have ⟨ho_ge, _⟩ : 1773 ≤ o ∧ o < codeBound := by
    simp only [isND, Bool.and_eq_true] at hNDo
    exact ⟨Nat.ble_eq.mp hNDo.1, Nat.blt_eq.mp hNDo.2⟩
  have ⟨hc_ge, _⟩ : 1773 ≤ c ∧ c < codeBound := by
    simp only [isND, Bool.and_eq_true] at hNDc
    exact ⟨Nat.ble_eq.mp hNDc.1, Nat.blt_eq.mp hNDc.2⟩
  set ao := o - 1773 with hao_def
  set ac := c - 1773 with hac_def
  have hao : ao < nNodes := by
    have hcb : codeBound = 64251 := rfl
    have hn : nNodes = 62478 := rfl
    omega
  have hac : ac < nNodes := by
    have hcb : codeBound = 64251 := rfl
    have hn : nNodes = 62478 := rfl
    omega
  have hCao := AllDensCentred ao hao
  have hCac := AllDensCentred ac hac
  have hoble : Nat.ble o 1 = false :=
    Bool.eq_false_iff.2 fun h => (by omega : ¬ o ≤ 1) (Nat.ble_eq.mp h)
  have hcble : Nat.ble c 1 = false :=
    Bool.eq_false_iff.2 fun h => (by omega : ¬ c ≤ 1) (Nat.ble_eq.mp h)
  have hPT_o : isPT o = false := by
    cases h : isPT o
    · rfl
    · have hlt : o < 1773 := by
        simp only [isPT, Bool.and_eq_true] at h; exact Nat.blt_eq.mp h.2
      omega
  have hPT_c : isPT c = false := by
    cases h : isPT c
    · rfl
    · have hlt : c < 1773 := by
        simp only [isPT, Bool.and_eq_true] at h; exact Nat.blt_eq.mp h.2
      omega
  have harg : argRel ao ac = true ∨ argRel ac ao = true := by
    simp only [nestOK, hoble, hcble, hNDo, hNDc, hPT_o, hPT_c, Bool.false_or, Bool.or_false,
      Bool.and_true, Bool.or_eq_true] at hnest
    simpa [ao, ac] using hnest
  have eo : o = 1773 + ao := by omega
  have ec : c = 1773 + ac := by omega
  have hPo : Pc o = Pnd (densSupG ao) := by
    rw [eo, Pc_of_ND ao (by omega), PndD]
  have hPc' : Pc c = Pnd (densSupG ac) := by
    rw [ec, Pc_of_ND ac (by omega), PndD]
  have hdo : dimCF o = dimF ao := by
    rw [eo, dimCF_of_ND (by omega)]
  have hdc : dimCF c = dimF ac := by
    rw [ec, dimCF_of_ND (by omega)]
  have hdimF : dimF ao < dimF ac := by
    rw [← hdo, ← hdc]
    exact hdim
  rcases harg with hfwd | hrev
  · have hland := densSup_land_mono_of_argRel_of_dim ao ac hao hac hfwd hdimF
    have hLe := Le_Pnd_of_land hCao hCac hland
    simpa [hPo, hPc'] using hLe
  · have hle : dimF ac ≤ dimF ao := argRel_dim_le hac hao hrev
    have : dimF ao < dimF ao := lt_of_lt_of_le hdimF hle
    exact (lt_irrefl _ this).elim
