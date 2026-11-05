-- Prove2me | solution 1 for GeneralPieces.Half.toN_ptn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:27:21.824117+00:00
-- url     : https://prove2.me/submissions/d17560d8-a552-4c27-af78-72ea3bf351ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_toL_toPNats

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : toN (ptn L) = (L : Multiset ℕ) := by
  have h : toN (ptn L) = ((toL (toPNats L) : List ℕ) : Multiset ℕ) := rfl
  rw [h, toL_toPNats hL]
end GeneralPieces.Half
