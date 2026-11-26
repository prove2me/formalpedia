-- Prove2me | solution 1 for N4Code.dRow12_flip2_eq_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:16.165815+00:00
-- url     : https://prove2.me/submissions/e1d4228f-97dd-4d72-a759-53ff6055044f

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_P2M_N4Code_sum_sub_two_zero__0b418aa7372d
import Theorems.Thm_P2M_N4Code_sum_sub_two_zero__142b88a159a7
import Theorems.Thm_N4Code_dRow_eq_mInd

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyeq : y t₁ = y t₂) :
    dRow C 1 (flipTwoBits t₁ t₂ y) = dRow C 1 y ∧
      dRow C 2 (flipTwoBits t₁ t₂ y) = dRow C 2 y := by
  cases hy : y t₁
  · have hy1 : y t₁ = false := hy
    have hy2 : y t₂ = false := by simpa [hy1] using hyeq
    constructor
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₁ (mInd C 1 (flipTwoBits t₁ t₂ y)) (mInd C 1 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₁ (mInd C 2 (flipTwoBits t₁ t₂ y)) (mInd C 2 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
  · have hy1 : y t₁ = true := hy
    have hy2 : y t₂ = true := by simpa [hy1] using hyeq
    constructor
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₂ (mInd C 1 (flipTwoBits t₁ t₂ y)) (mInd C 1 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₂ (mInd C 2 (flipTwoBits t₁ t₂ y)) (mInd C 2 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
end N4Code
