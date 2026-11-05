-- Prove2me | solution 1 for GeneralPieces.Ring.op_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:18:29.830128+00:00
-- url     : https://prove2.me/submissions/56d08eb0-02ca-4746-af04-e914fc4ccb53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (a : V) (r : ℤ) (f : V) {S : Finset (ℕ+ →₀ ℕ)} (hS : a.support ⊆ S) :
    op a r f = ∑ m ∈ S, coeff m a • opMon (Finsupp.toMultiset m).toList r f := by
  unfold op
  refine sum_subset hS fun m _ hm => ?_
  rw [notMem_support_iff.1 hm, zero_smul]
end GeneralPieces.Ring
