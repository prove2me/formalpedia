-- Prove2me | solution 1 for GeneralPieces.Dual.tpow_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:16:19.861195+00:00
-- url     : https://prove2.me/submissions/fe7f9717-71d7-4e20-ba3a-8cb8bf82a7cc

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
theorem _root_.solution (a : ℕ+) (l : List ℕ+) : tpow ((a :: l : List ℕ+) : Multiset ℕ+) = X a * tpow (l : Multiset ℕ+) := by
  unfold tpow
  rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]
end GeneralPieces.Dual
