-- Prove2me | solution 1 for GeneralPieces.Dual.zz_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:21:03.764967+00:00
-- url     : https://prove2.me/submissions/91a97f8c-c0b1-4677-ac91-b30288024037

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
theorem _root_.solution {ν : Ptn} {S : Finset ℕ+} (h : ν.toFinset ⊆ S) : zz ν = ∏ k ∈ S, (k : ℕ) ^ ν.count k * (ν.count k).factorial := by
  unfold zz
  refine prod_subset h fun k _ hk => ?_
  rw [Multiset.count_eq_zero_of_notMem fun h' => hk (Multiset.mem_toFinset.2 h')]
  simp
end GeneralPieces.Dual
