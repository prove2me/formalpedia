-- Prove2me | solution 1 for GeneralPieces.Dual.weight_toFinsupp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:21:10.972184+00:00
-- url     : https://prove2.me/submissions/c4dfd435-8cd5-4ade-9e6a-05e5bb9c3aa1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (ν : Ptn) : Finsupp.weight (fun k : ℕ+ => (k : ℕ)) (Multiset.toFinsupp ν) = wt ν := by
  induction ν using Multiset.induction_on with
  | empty => simp [wt]
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, map_add, ih, Multiset.toFinsupp_singleton]
    simp [wt, Finsupp.weight_apply]
end GeneralPieces.Dual
