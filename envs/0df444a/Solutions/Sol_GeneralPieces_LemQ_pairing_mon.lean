-- Prove2me | solution 1 for GeneralPieces.LemQ.pairing_mon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:14:53.675006+00:00
-- url     : https://prove2.me/submissions/82cd5a5a-f01c-44c5-a92d-8d2ba00c43a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_coef_op_tpow

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (hB : StBridge) (hOp : OpFacts) (h : ℕ) (μ ν : Ptn) :
    pairing h (tpow μ) (tpow ν) = (ClauseBound.Boson.op (lst μ) (-(h : ℤ)) 0 (toN ν) : ℚ) := by
  have e := coef_op_tpow hB hOp μ (-(h : ℤ)) 0 ν
  unfold coef at e
  rw [map_zero] at e
  exact e
end GeneralPieces.LemQ
