-- Prove2me | solution 1 for GeneralPieces.Pcs.X_eq_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:27.527583+00:00
-- url     : https://prove2.me/submissions/0e1613d7-f608-4627-a163-f409731a610c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (k : ℕ+) : (X k : V) = tpow {k} := by
  unfold tpow
  rw [Multiset.toFinsupp_singleton]
  rfl
end GeneralPieces.Pcs
