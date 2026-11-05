-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.three_le_eL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:33:31.117986+00:00
-- url     : https://prove2.me/submissions/23c3beb6-c0f1-4ca2-a415-f0b402d3e430

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
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (h : ℕ) : 3 * h + 12 * h ^ 2 ≤ ClauseBound.Boson.Half.eL h := by
  unfold ClauseBound.Boson.Half.eL
  nlinarith
end GeneralPieces.ThmHalfPieces
