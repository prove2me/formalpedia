-- Prove2me | solution 1 for GeneralPieces.Half.sum_Icc_eq_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:43:30.020752+00:00
-- url     : https://prove2.me/submissions/45dac335-19aa-4dc4-b2be-d1a4964b96f8

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
theorem _root_.solution (f : ℕ → V) (n : ℕ) : ∑ j ∈ Icc 1 n, f j = ((List.range n).map fun i => f (i + 1)).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, List.range_succ, List.map_append, List.sum_append]; simp
end GeneralPieces.Half
