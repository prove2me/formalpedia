-- Prove2me | solution 1 for N4Code.dRow12_flip2_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:45.682796+00:00
-- url     : https://prove2.me/submissions/cce4a377-442d-4ce5-95ba-8b6ac525961c

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_sum_sub_two_neg
import Theorems.Thm_N4Code_dRow_eq_mInd

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dRow C 1 (flipTwoBits t₁ t₂ y) + 2 = dRow C 1 y ∧
      dRow C 2 (flipTwoBits t₁ t₂ y) + 2 = dRow C 2 y := by
  constructor
  · rw [dRow_eq_mInd, dRow_eq_mInd]
    exact sum_sub_two_neg (mInd C 1 (flipTwoBits t₁ t₂ y)) (mInd C 1 y) t₁ t₂ htne
      (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
      (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
      (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
  · rw [dRow_eq_mInd, dRow_eq_mInd]
    exact sum_sub_two_neg (mInd C 2 (flipTwoBits t₁ t₂ y)) (mInd C 2 y) t₁ t₂ htne
      (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
      (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
      (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
end N4Code
