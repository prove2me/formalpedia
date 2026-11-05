-- Prove2me | solution 1 for GeneralPieces.Series.bet_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:13.31272+00:00
-- url     : https://prove2.me/submissions/322bd657-f3a6-47d3-8aad-ad6b7cc7f4a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
import Theorems.Thm_ClauseBound_Boson_Scalars_choose_eq_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
namespace GeneralPieces.Series
theorem _root_.solution {n l : ℕ} (h : l < n) : bet n l = 0 := by
  unfold bet
  split_ifs with h0
  · rfl
  · exact Scalars.choose_eq_zero (by omega) (by omega)
end GeneralPieces.Series
