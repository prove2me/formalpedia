-- Prove2me | solution 1 for GeneralPieces.Sizes.bet_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:27:43.588576+00:00
-- url     : https://prove2.me/submissions/bb6b8ce4-002f-49a3-92fb-8081367c5526

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Ring_binom_natCast


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (n : ℕ+) {r : ℤ} (hr : r ≠ 0) : ClauseBound.Boson.bet n r = binom (r - 1) ((n : ℤ) - 1) := by
  have e2 : ((n : ℕ) : ℤ) - 1 = (((n : ℕ) - 1 : ℕ) : ℤ) := by have := n.pos; omega
  rw [ClauseBound.Boson.bet, if_neg hr, e2, binom_natCast]
end GeneralPieces.Sizes
