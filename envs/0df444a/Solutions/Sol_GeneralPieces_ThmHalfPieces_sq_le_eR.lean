-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.sq_le_eR
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:31:56.568794+00:00
-- url     : https://prove2.me/submissions/b1a5059f-c069-437e-b7af-0cf95e6dd3f2

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

theorem solution (h : ℕ) : h * h + 12 * h ^ 2 ≤ ClauseBound.Boson.Half.eR h := by
  unfold ClauseBound.Boson.Half.eR
  nlinarith
