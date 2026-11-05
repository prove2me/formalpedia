-- Prove2me | solution 1 for GeneralPieces.Half.polyK_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:41:55.118111+00:00
-- url     : https://prove2.me/submissions/ab46c1b2-fcb9-4776-9ff2-384e3554b189

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution (k : ℤ × List ℕ → ℚ) (A B : ClauseBound.Boson.FA) : polyK k (A ++ B) = polyK k A + polyK k B := by
  simp [polyK]
end GeneralPieces.Half
