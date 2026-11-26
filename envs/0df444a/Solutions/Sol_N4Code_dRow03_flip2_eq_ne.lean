-- Prove2me | solution 1 for N4Code.dRow03_flip2_eq_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:43.437292+00:00
-- url     : https://prove2.me/submissions/b6b47cf2-93ea-46b3-bc17-498aaa7e0ddd

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_bool_ne_cases
import Theorems.Thm_P2M_N4Code_sum_sub_two_zero__0b418aa7372d
import Theorems.Thm_P2M_N4Code_sum_sub_two_zero__142b88a159a7
import Theorems.Thm_N4Code_dRow_eq_mInd

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyne : y t₁ ≠ y t₂) :
    dRow C 0 (flipTwoBits t₁ t₂ y) = dRow C 0 y ∧
      dRow C 3 (flipTwoBits t₁ t₂ y) = dRow C 3 y := by
  rcases bool_ne_cases hyne with hy | hy
  · rcases hy with ⟨hy1, hy2⟩
    constructor
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₂ (mInd C 0 (flipTwoBits t₁ t₂ y)) (mInd C 0 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₁ (mInd C 3 (flipTwoBits t₁ t₂ y)) (mInd C 3 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
  · rcases hy with ⟨hy1, hy2⟩
    constructor
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₁ (mInd C 0 (flipTwoBits t₁ t₂ y)) (mInd C 0 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₂ (mInd C 3 (flipTwoBits t₁ t₂ y)) (mInd C 3 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
end N4Code
