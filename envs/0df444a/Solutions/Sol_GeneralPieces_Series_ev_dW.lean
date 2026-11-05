-- Prove2me | solution 1 for GeneralPieces.Series.ev_dW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:37.664185+00:00
-- url     : https://prove2.me/submissions/0eee71ba-9984-4b4b-bd85-7426541173bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Theorems.Thm_GeneralPieces_Series_ev_W

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
theorem _root_.solution : ev dW = 0 := by rw [dW, map_sub, ev_W, ev_W, sub_self]
end GeneralPieces.Series
