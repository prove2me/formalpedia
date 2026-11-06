-- Prove2me | solution 2 for GeneralPieces.ThmHalfPieces.three_le_eL
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:19:46.518191+00:00
-- url     : https://prove2.me/submissions/170c2a41-5440-4901-b4fb-6a0e559ef3e1

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

theorem solution (h : ℕ) : 3 * h + 12 * h ^ 2 ≤ ClauseBound.Boson.Half.eL h := by
  unfold ClauseBound.Boson.Half.eL
  nlinarith
