-- Prove2me | solution 1 for GeneralPieces.LemQ.op_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:23.084674+00:00
-- url     : https://prove2.me/submissions/b6d427b7-b862-4050-9d13-3e954bee7c99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (hOp : OpFacts) (a : V) (r : ℤ) (S : Finset Ptn) (q : Ptn → ℚ) :
    op a r (∑ μ ∈ S, q μ • tpow μ) = ∑ μ ∈ S, q μ • op a r (tpow μ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := hOp.smul_right a r 0 0
    simpa using this
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, hOp.add_right, hOp.smul_right, ih]
end GeneralPieces.LemQ
