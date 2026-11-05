-- Prove2me | solution 2 for GeneralPieces.Pcs.isInt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:25:51.830463+00:00
-- url     : https://prove2.me/submissions/1d1c8f49-7ba1-4a3e-8f9b-8847c42202d2

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
theorem _root_.solution : IsInt (0 : V) := fun m => ⟨0, by simp⟩
end GeneralPieces.Pcs
