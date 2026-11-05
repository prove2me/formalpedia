-- Prove2me | solution 1 for GeneralPieces.Sizes.abs_binom_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:27:54.046751+00:00
-- url     : https://prove2.me/submissions/c35d1671-b7c9-4b39-bef0-44b2568ff01a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_ClauseBound_Rec_abs_choose_le
import Theorems.Thm_GeneralPieces_Ring_binom_natCast


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (k : ℤ) (n : ℕ+) : |binom k ((n : ℤ) - 1)| ≤ 2 ^ (k.natAbs + ((n : ℕ) - 1)) := by
  have e2 : ((n : ℕ) : ℤ) - 1 = (((n : ℕ) - 1 : ℕ) : ℤ) := by have := n.pos; omega
  rw [e2, binom_natCast]
  exact ClauseBound.Rec.abs_choose_le _ _
end GeneralPieces.Sizes
