-- Prove2me | solution 1 for N4Code.dRow12_flip2_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:28.322835+00:00
-- url     : https://prove2.me/submissions/9646c515-31cf-4e09-ae7c-37ef077187d9

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_sum_sub_two_pos
import Theorems.Thm_N4Code_dRow_eq_mInd

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dRow C 1 (flipTwoBits t₁ t₂ y) = dRow C 1 y + 2 ∧
      dRow C 2 (flipTwoBits t₁ t₂ y) = dRow C 2 y + 2 := by
  constructor
  · rw [dRow_eq_mInd, dRow_eq_mInd]
    exact sum_sub_two_pos (mInd C 1 (flipTwoBits t₁ t₂ y)) (mInd C 1 y) t₁ t₂ htne
      (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
      (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
      (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
  · rw [dRow_eq_mInd, dRow_eq_mInd]
    exact sum_sub_two_pos (mInd C 2 (flipTwoBits t₁ t₂ y)) (mInd C 2 y) t₁ t₂ htne
      (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
      (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
      (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
end N4Code
