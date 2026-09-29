-- Prove2me | solution 1 for MagicSquares.normal_order_three_constant
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T14:06:11.460929+00:00
-- url     : https://prove2.me/submissions/1f1e874a-1041-4f5f-8a33-e876ce6e0626

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_magic_constant_of_normal

set_option autoImplicit false

open MagicSquares

/-- Reduction of `MagicSquares.normal_order_three_constant` to
`MagicSquares.magic_constant_of_normal`.

For a normal square the general identity gives `2 * s = n (n²+1)`; putting `n = 3`
yields `2 s = 30`, hence `s = 15`. -/
theorem solution (M : Square 3 ℕ) (s : ℕ) (hN : IsNormal M) (hM : IsMagic M s) :
    s = 15 := by
  have h := magic_constant_of_normal 3 M s hN hM
  norm_num at h
  omega
