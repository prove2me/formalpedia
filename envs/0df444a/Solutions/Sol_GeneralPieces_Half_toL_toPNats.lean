-- Prove2me | solution 1 for GeneralPieces.Half.toL_toPNats
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:25:54.109899+00:00
-- url     : https://prove2.me/submissions/2bdefcd5-c93f-450f-9d95-a4dbc36b160e

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
theorem _root_.solution {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : toL (toPNats L) = L := by
  unfold toL toPNats
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun k hk => PNat.toPNat'_coe (hL k hk)
end GeneralPieces.Half
