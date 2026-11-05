-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.card_ptnsZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:40:42.940817+00:00
-- url     : https://prove2.me/submissions/ef8e12f3-6a6b-4fe0-ada4-d822365b5fa8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_Ring_card_ptns


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (m : ℤ) : #(ptnsZ m) = pZ m := by
  unfold ptnsZ pZ
  split_ifs
  · exact card_ptns _
  · exact card_empty
end GeneralPieces.ThmHalfPieces
