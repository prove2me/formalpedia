-- Prove2me | solution 1 for GeneralPieces.Sizes.pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:29:19.4992+00:00
-- url     : https://prove2.me/submissions/87536f21-32ba-48bc-9846-9e2d11498689

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
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) : (32 * h ^ 2 * 2 ^ (5 * h)) ^ h ≤ 2 ^ (12 * h ^ 2) := by
  have a1 : h ^ 2 ≤ 2 ^ (2 * h) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
  have a2 : 32 ≤ 2 ^ (5 * h) := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (5 * h) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (32 * h ^ 2 * 2 ^ (5 * h)) ^ h ≤ (2 ^ (5 * h) * 2 ^ (2 * h) * 2 ^ (5 * h)) ^ h :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul a2 a1)) h
    _ = 2 ^ (12 * h ^ 2) := by rw [← pow_add, ← pow_add, ← pow_mul]; congr 1; ring
end GeneralPieces.Sizes
