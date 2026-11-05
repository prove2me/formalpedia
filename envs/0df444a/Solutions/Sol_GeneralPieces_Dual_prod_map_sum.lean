-- Prove2me | solution 1 for GeneralPieces.Dual.prod_map_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:16:04.571233+00:00
-- url     : https://prove2.me/submissions/a326ebe3-1062-4951-8a07-2b862580f1d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_sum_tuples_cons

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution {ι α R : Type} [DecidableEq α] [CommSemiring R] (L : List ι) (S : ι → Finset α) (f : ι → α → R) :
    (L.map fun i => ∑ a ∈ S i, f i a).prod = ∑ x ∈ tuples (L.map S), (List.zipWith f L x).prod := by
  induction L with
  | nil => simp [tuples]
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, sum_tuples_cons, sum_mul_sum]
    simp only [List.zipWith_cons_cons, List.prod_cons]
end GeneralPieces.Dual
