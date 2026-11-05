-- Prove2me | solution 1 for GeneralPieces.Ring.op_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:42:51.932026+00:00
-- url     : https://prove2.me/submissions/e06af931-c5a4-4802-af52-1b279880317e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_opMon_perm

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (r : ℤ) (f : V) : op (tpow (μ : Multiset ℕ+)) r f = opMon μ r f := by
  unfold op tpow
  rw [support_monomial, if_neg one_ne_zero, sum_singleton, coeff_monomial, if_pos rfl, one_smul, Multiset.toFinsupp_toMultiset]
  exact opMon_perm (Multiset.coe_eq_coe.1 (Multiset.coe_toList _)) r f
end GeneralPieces.Ring
