-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.bound_lt_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:16.006231+00:00
-- url     : https://prove2.me/submissions/e45b0ce5-700d-436c-b5fe-fbbf61e7ec0e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (h : ℕ) : Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) < 2 ^ ClauseBound.Boson.big h := by
  have a1 : Delta h ≤ 2 ^ Nat.clog 2 (Delta h) := Nat.le_pow_clog (by norm_num) _
  have a2 : h.factorial ≤ 2 ^ (h * h) := (Nat.factorial_le_pow h).trans (by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le h)
  have a3 : 3 * h + 12 * h ^ 2 + (h * h + 12 * h ^ 2) < 40 * (h + 1) ^ 2 := by nlinarith
  have a4 : ClauseBound.Boson.big h = 40 * (h + 1) ^ 2 + Nat.clog 2 (Delta h) := rfl
  calc _ ≤ 2 ^ Nat.clog 2 (Delta h) * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (2 ^ (h * h) * 2 ^ (12 * h ^ 2))) :=
        Nat.mul_le_mul a1 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ a2))
    _ = 2 ^ (Nat.clog 2 (Delta h) + (3 * h + 12 * h ^ 2 + (h * h + 12 * h ^ 2))) := by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ < 2 ^ ClauseBound.Boson.big h := Nat.pow_lt_pow_right (by norm_num) (by rw [a4]; linarith)
end GeneralPieces.ThmHalfPieces
