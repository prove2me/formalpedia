-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.nestOK_symm
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:46:17.093424+00:00
-- url     : https://prove2.me/submissions/9cc793f6-8879-4e3f-bc96-b7da417b7543

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

private theorem isND_eq_true {x : ℕ} : isND x = true ↔ 1773 ≤ x ∧ x < codeBound := by
  constructor
  · intro h
    simp only [isND, Bool.and_eq_true] at h
    exact ⟨Nat.ble_eq.mp h.1, Nat.blt_eq.mp h.2⟩
  · intro ⟨h1, h2⟩
    simp only [isND, Bool.and_eq_true]
    exact ⟨Nat.ble_eq.mpr h1, Nat.blt_eq.mpr h2⟩

private theorem isPT_eq_true {x : ℕ} : isPT x = true ↔ 2 ≤ x ∧ x < 1773 := by
  constructor
  · intro h
    simp only [isPT, Bool.and_eq_true] at h
    exact ⟨Nat.ble_eq.mp h.1, Nat.blt_eq.mp h.2⟩
  · intro ⟨h1, h2⟩
    simp only [isPT, Bool.and_eq_true]
    exact ⟨Nat.ble_eq.mpr h1, Nat.blt_eq.mpr h2⟩

private theorem not_isPT_of_isND {x : ℕ} (h : isND x = true) : isPT x = false := by
  have ⟨hge, _⟩ := isND_eq_true.1 h
  cases hPT : isPT x
  · rfl
  · have ⟨_, hlt⟩ := isPT_eq_true.1 hPT
    omega

theorem solution (o c : ℕ) : nestOK o c = nestOK c o := by
  cases ho1 : Nat.ble o 1 <;> cases hc1 : Nat.ble c 1
  · cases hNDo : isND o <;> cases hNDc : isND c
    · simp [nestOK, ho1, hc1, hNDo, hNDc]
    · have hPTc : isPT c = false := not_isPT_of_isND hNDc
      simp [nestOK, ho1, hc1, hNDo, hNDc, hPTc, Bool.and_comm]
    · have hPTo : isPT o = false := not_isPT_of_isND hNDo
      simp [nestOK, ho1, hc1, hNDo, hNDc, hPTo, Bool.and_comm]
    · have hPTo : isPT o = false := not_isPT_of_isND hNDo
      have hPTc : isPT c = false := not_isPT_of_isND hNDc
      simp [nestOK, ho1, hc1, hNDo, hNDc, hPTo, hPTc]
      exact Bool.or_comm _ _
  · simp [nestOK, ho1, hc1]
  · simp [nestOK, ho1, hc1]
  · simp [nestOK, ho1, hc1]
