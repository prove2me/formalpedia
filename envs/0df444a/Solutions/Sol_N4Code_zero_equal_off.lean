-- Prove2me | solution 1 for N4Code.zero_equal_off
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:17.281699+00:00
-- url     : https://prove2.me/submissions/3f837615-067f-4cec-ac26-4f5cd0503be8

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRowMin_flip_eq
import Theorems.Thm_N4Code_dCode_replace_0
import Theorems.Thm_N4Code_dCode_eq_min_dOc_dPc

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n)
    (hnot : ¬ Y3c C s' hO hP t y) :
    dCode C y = dCode (replaceColumn C t s') (g0 C s' hO hP t y) := by
  have hdC : dCode C y = min (dOc C s' hO y) (dPc C s' hP y) :=
    dCode_eq_min_dOc_dPc C s' hO hP y
  by_cases hyt : y t = true
  · have hneq : dOc C s' hO y ≠ dPc C s' hP y := by
      intro h
      exact hnot ⟨hyt, h⟩
    by_cases hle : dOc C s' hO y ≤ dPc C s' hP y
    · have hlt : dOc C s' hO y < dPc C s' hP y := lt_of_le_of_ne hle hneq
      have hg0 : g0 C s' hO hP t y = y := by simp [g0, hle]
      have hdP := (dRowMin_flip_eq C (colOnes s') hP t y hcol).1 hyt
      have hdC' : dCode (replaceColumn C t s') y = dOc C s' hO y := by
        rw [dCode_replace_0 C t s' hcol hO hP y]
        change min (dOc C s' hO y) (dRowMin C (colOnes s') hP (flipBit t y)) = dOc C s' hO y
        rw [hdP]
        change min (dOc C s' hO y) (dPc C s' hP y - 1) = dOc C s' hO y
        have hle' : dOc C s' hO y ≤ dPc C s' hP y - 1 := by omega
        rw [min_eq_left hle']
      rw [hdC, hg0, hdC']
      rw [min_eq_left hle]
    · have hgt : dPc C s' hP y < dOc C s' hO y := lt_of_not_ge hle
      have hg0 : g0 C s' hO hP t y = flipBit t y := by simp [g0, hle]
      have hdO := (dRowMin_flip_eq C (colZeros s') hO t y hcol).1 hyt
      have hdC' : dCode (replaceColumn C t s') (flipBit t y) = dPc C s' hP y := by
        rw [dCode_replace_0 C t s' hcol hO hP (flipBit t y)]
        change min (dRowMin C (colZeros s') hO (flipBit t y))
            (dPc C s' hP (flipBit t (flipBit t y))) = dPc C s' hP y
        rw [hdO, flipBit_involutive]
        change min (dOc C s' hO y - 1) (dPc C s' hP y) = dPc C s' hP y
        have hle' : dPc C s' hP y ≤ dOc C s' hO y - 1 := by omega
        rw [min_eq_right hle']
      rw [hdC, hg0, hdC']
      rw [min_eq_right (le_of_lt hgt)]
  · have hytf : y t = false := by
      simpa using hyt
    by_cases hle : dOc C s' hO y ≤ dPc C s' hP y
    · have hg0 : g0 C s' hO hP t y = y := by simp [g0, hle]
      have hdP := (dRowMin_flip_eq C (colOnes s') hP t y hcol).2 hytf
      have hdC' : dCode (replaceColumn C t s') y = dOc C s' hO y := by
        rw [dCode_replace_0 C t s' hcol hO hP y]
        change min (dOc C s' hO y) (dRowMin C (colOnes s') hP (flipBit t y)) = dOc C s' hO y
        rw [hdP]
        change min (dOc C s' hO y) (dPc C s' hP y + 1) = dOc C s' hO y
        rw [min_eq_left (le_trans hle (by omega))]
      rw [hdC, hg0, hdC']
      rw [min_eq_left hle]
    · have hgt : dPc C s' hP y < dOc C s' hO y := lt_of_not_ge hle
      have hg0 : g0 C s' hO hP t y = flipBit t y := by simp [g0, hle]
      have hdO := (dRowMin_flip_eq C (colZeros s') hO t y hcol).2 hytf
      have hdC' : dCode (replaceColumn C t s') (flipBit t y) = dPc C s' hP y := by
        rw [dCode_replace_0 C t s' hcol hO hP (flipBit t y)]
        change min (dRowMin C (colZeros s') hO (flipBit t y))
            (dPc C s' hP (flipBit t (flipBit t y))) = dPc C s' hP y
        rw [hdO, flipBit_involutive]
        change min (dOc C s' hO y + 1) (dPc C s' hP y) = dPc C s' hP y
        rw [min_eq_right (by omega)]
      rw [hdC, hg0, hdC']
      rw [min_eq_right (le_of_lt hgt)]
end N4Code
