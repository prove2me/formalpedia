-- Prove2me | solution 1 for GeneralPieces.Dual.tpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:03:10.509699+00:00
-- url     : https://prove2.me/submissions/86cfe4f0-ef92-4cd8-bfae-b65eabfb0a14

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

private theorem weight_toFinsupp_aux (ν : Ptn) :
    Finsupp.weight (fun k : ℕ+ => (k : ℕ)) (Multiset.toFinsupp ν) = wt ν := by
  induction ν using Multiset.induction_on with
  | empty => simp [wt]
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, map_add, ih,
      Multiset.toFinsupp_singleton]
    simp [wt, Finsupp.weight_apply]

theorem solution (ν : Ptn) : tpow ν ∈ VE (wt ν) := by
  rw [VE, if_pos (Int.natCast_nonneg _), Int.toNat_natCast, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_toFinsupp_aux ν)
