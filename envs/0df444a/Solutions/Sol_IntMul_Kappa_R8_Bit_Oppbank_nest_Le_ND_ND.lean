-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND_ND
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:08:43.663982+00:00
-- url     : https://prove2.me/submissions/0c6e412d-af8d-4424-bcd8-b079f1d1bb5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Le_Pnd_of_land
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_eq_of_Le_dimrev
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      isND o = true → isND c = true → dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
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
  rcases harg with h | h
  · have hLe := Le_Pnd_of_land hCao hCac (densSup_land_mono_of_argRel ao ac hao hac h)
    simpa [hPo, hPc'] using hLe
  · have hLe : Le (Pc c) (Pc o) := by
      simpa [hPo, hPc'] using
        Le_Pnd_of_land hCac hCao (densSup_land_mono_of_argRel ac ao hac hao h)
    have e : Pc c = Pc o := Pc_eq_of_Le_dimrev hc ho hLe hdim
    have hidem := Pc_idem ho
    rw [← e] at hidem ⊢
    exact ⟨hidem, hidem⟩
