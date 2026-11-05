-- Prove2me | solution 1 for GeneralPieces.Half.aFam_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:46:16.07262+00:00
-- url     : https://prove2.me/submissions/e129f294-c832-4d9c-94ea-c31a1d7d455b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_ptn_cons
import Theorems.Thm_GeneralPieces_Half_polyOf_flatMap
import Theorems.Thm_GeneralPieces_Half_sum_yl

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : AppHalfPieces.aFam (ptn L) = polyOf (ClauseBound.Boson.aFam L) := by
  induction L with
  | nil => simp [AppHalfPieces.aFam, ptn, toPNats, polyOf, polyK, ClauseBound.Boson.aFam, tpow]
  | cons n L ih =>
    rw [ClauseBound.Boson.aFam, polyOf_flatMap, sum_yl (hL n List.mem_cons_self), ← ih fun m hm => hL m (List.mem_cons_of_mem _ hm), ptn_cons, AppHalfPieces.aFam,
      Multiset.map_cons, Multiset.prod_cons, AppHalfPieces.aFam]
end GeneralPieces.Half
