-- Prove2me | solution 1 for KernelRamsey.testBit_complementRows
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:45:01.302596+00:00
-- url     : https://prove2.me/submissions/9c0bf48a-e3d8-4e35-958b-b2cc294c6282

import Mathlib
import Definitions.Def_KernelRamsey_Mask
open KernelRamsey

theorem row_complementRows {n : Nat} (rows : List Nat) (i : Fin n) :
    row (complementRows n rows) i.val = (fullMask n ^^^ row rows i.val) &&& (fullMask n ^^^ 2 ^ i.val) := by
  unfold row complementRows
  simp [List.getD_eq_getElem?_getD, i.isLt, row]

theorem solution {n : Nat} (rows : List Nat) (i j : Fin n) :
    (row (complementRows n rows) i.val).testBit j.val =
      (!(row rows i.val).testBit j.val && decide (i.val ≠ j.val)) := by
  rw [row_complementRows, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_two_pow,
    fullMask, Nat.testBit_two_pow_sub_one]
  simp [j.isLt]
