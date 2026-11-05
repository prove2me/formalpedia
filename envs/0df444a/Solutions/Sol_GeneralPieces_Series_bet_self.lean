-- Prove2me | solution 1 for GeneralPieces.Series.bet_self
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:07:15.018291+00:00
-- url     : https://prove2.me/submissions/70bbf4c7-d033-4d33-8754-2937407a2ef9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset

theorem solution {n : ℕ} (h : 1 ≤ n) : bet n n = 1 := by
  rw [bet, if_neg (by omega : (n : ℤ) ≠ 0)]
  rw [show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega]
  rw [Ring.choose_natCast, Nat.choose_self]
  simp
