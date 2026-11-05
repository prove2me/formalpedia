-- Prove2me | solution 1 for GeneralPieces.LemQ.coef_op_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:22.084664+00:00
-- url     : https://prove2.me/submissions/2bb0cd51-8efc-4b76-866f-01d781c01879

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
theorem _root_.solution (hB : StBridge) (hOp : OpFacts) (μ : Ptn) (r : ℤ) (π σ : Ptn) :
    coef π (op (tpow μ) r (tpow σ)) = (ClauseBound.Boson.op (lst μ) r (toN π) (toN σ) : ℚ) := by
  have h := hOp.mono μ.toList r (tpow σ)
  rw [Multiset.coe_toList] at h
  rw [h]
  exact hB _ _ _ _
end GeneralPieces.LemQ
