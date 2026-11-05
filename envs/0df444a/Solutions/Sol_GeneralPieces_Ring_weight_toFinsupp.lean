-- Prove2me | solution 1 for GeneralPieces.Ring.weight_toFinsupp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:53.060432+00:00
-- url     : https://prove2.me/submissions/0ea0d597-9a1c-49b2-a146-200eb0075c4a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : Ptn) : Finsupp.weight wgt (Multiset.toFinsupp μ) = wt μ := by
  induction μ using Multiset.induction_on with
  | empty => simp [wt]
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add, map_add, ih, Multiset.toFinsupp_singleton, Finsupp.weight_single]
    simp [wt, wgt]
end GeneralPieces.Ring
