-- Prove2me | solution 1 for GeneralPieces.Sizes.length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:29:12.395633+00:00
-- url     : https://prove2.me/submissions/456c6333-9c9b-44dc-9738-a9cc8428e47b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_card_le_wt
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (a : List ℕ+) : a.length ≤ (toL a).sum := by
  have := card_le_wt (a : Multiset ℕ+)
  simpa [wt, toL] using this
end GeneralPieces.Sizes
