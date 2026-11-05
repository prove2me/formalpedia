-- Prove2me | solution 1 for GeneralPieces.Half.wt_ptn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:28:33.549814+00:00
-- url     : https://prove2.me/submissions/1721195a-5b38-4057-acde-bd8326974974

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_toN_ptn
import Theorems.Thm_GeneralPieces_Ring_sum_toN


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : wt (ptn L) = L.sum := by
  rw [← sum_toN, toN_ptn hL, Multiset.sum_coe]
end GeneralPieces.Half
