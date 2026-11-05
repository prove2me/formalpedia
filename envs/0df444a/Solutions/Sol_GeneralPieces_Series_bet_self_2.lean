-- Prove2me | solution 2 for GeneralPieces.Series.bet_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:07:58.481708+00:00
-- url     : https://prove2.me/submissions/47e7b2ee-1a6d-4296-b37c-765ac725e2e8

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
namespace GeneralPieces.Series
theorem _root_.solution {n : ℕ} (h : 1 ≤ n) : bet n n = 1 := by
  unfold bet
  rw [if_neg (by omega), show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
end GeneralPieces.Series
