-- Prove2me | solution 2 for GeneralPieces.Sizes.length_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:29:48.074194+00:00
-- url     : https://prove2.me/submissions/be3e7f09-4a19-44f4-a135-3e4b340d7bac

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

theorem solution (a : List ℕ+) : a.length ≤ (toL a).sum := by
  induction a with
  | nil => simp [toL]
  | cons n a ih =>
    simp only [toL, List.map_cons, List.length_cons, List.sum_cons] at *
    have hn : 0 < (n : ℕ) := n.pos
    omega
