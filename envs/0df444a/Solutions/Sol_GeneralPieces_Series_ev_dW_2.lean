-- Prove2me | solution 2 for GeneralPieces.Series.ev_dW
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:23:08.781675+00:00
-- url     : https://prove2.me/submissions/854e9c38-37d4-4d8a-92db-847a5e8d9094

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}

private theorem ev_W_aux (x y : ℤ) : ev (W x y) = 1 := by
  rw [ev, W, AddMonoidAlgebra.lift_single]
  simp

theorem solution : ev dW = 0 := by
  rw [dW, map_sub, ev_W_aux, ev_W_aux, sub_self]
