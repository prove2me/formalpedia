-- Prove2me | solution 2 for GeneralPieces.Sizes.pow_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:23:47.163068+00:00
-- url     : https://prove2.me/submissions/d19d6c52-ae7d-4b17-b5d2-66bdc6cafea7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem solution {h : ℕ} (hh : 1 ≤ h) : (32 * h ^ 2 * 2 ^ (5 * h)) ^ h ≤ 2 ^ (12 * h ^ 2) := by
  have hsq : h ^ 2 ≤ 2 ^ (2 * h) := by
    calc
      h ^ 2 ≤ (2 ^ h) ^ 2 := Nat.pow_le_pow_left h.lt_two_pow_self.le 2
      _ = 2 ^ (2 * h) := by rw [← pow_mul, Nat.mul_comm]
  calc
    (32 * h ^ 2 * 2 ^ (5 * h)) ^ h
        ≤ (32 * 2 ^ (2 * h) * 2 ^ (5 * h)) ^ h := by gcongr
    _ = 2 ^ ((5 + 7 * h) * h) := by
      rw [show 32 = 2 ^ 5 by norm_num, ← pow_add, ← pow_add, ← pow_mul]
      congr 2
      ring
    _ ≤ 2 ^ (12 * h ^ 2) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith [Nat.mul_le_mul_left h hh]
