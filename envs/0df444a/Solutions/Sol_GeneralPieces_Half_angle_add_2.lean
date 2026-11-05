-- Prove2me | solution 2 for GeneralPieces.Half.angle_add
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:45:41.290202+00:00
-- url     : https://prove2.me/submissions/d2f6ad4b-cb6f-4543-8634-5d1cff16fedb

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

theorem solution (h i : ℕ) (a b : V) : angle h i (a + b) = angle h i a + angle h i b := by
  simp only [angle, part, map_add, smul_add, Finset.sum_add_distrib]
