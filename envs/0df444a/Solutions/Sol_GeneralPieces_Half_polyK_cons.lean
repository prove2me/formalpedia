-- Prove2me | solution 1 for GeneralPieces.Half.polyK_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:25:55.552338+00:00
-- url     : https://prove2.me/submissions/501ae6fe-77f9-4a93-8b31-b9052a7efca8

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
theorem _root_.solution (k : ℤ × List ℕ → ℚ) (c : ℤ × List ℕ) (A : ClauseBound.Boson.FA) : polyK k (c :: A) = k c • tpow (ptn c.2) + polyK k A := by
  simp [polyK]
end GeneralPieces.Half
