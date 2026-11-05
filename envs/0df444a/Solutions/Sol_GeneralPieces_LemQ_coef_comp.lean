-- Prove2me | solution 1 for GeneralPieces.LemQ.coef_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:15:12.638515+00:00
-- url     : https://prove2.me/submissions/b3fac8c3-d6cf-4116-b71e-e1fc42dbe0f0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_coef_sum
import Theorems.Thm_GeneralPieces_LemQ_eq_sum_ptnsZ
import Theorems.Thm_GeneralPieces_LemQ_coef_op_tpow
import Theorems.Thm_GeneralPieces_LemQ_sum_Pz
import Theorems.Thm_GeneralPieces_LemQ_op_sum_right
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_smul
import Theorems.Thm_GeneralPieces_Ring_sum_toN
import Theorems.Thm_GeneralPieces_Ring_tpow_mem_VE


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (hB : StBridge) (hOp : OpFacts) (h1 : O1) (μ ν : Ptn) (r r' : ℤ) (π σ : Ptn) :
    coef π (op (tpow μ) r (op (tpow ν) r' (tpow σ))) = (ClauseBound.Boson.mul2 (lst μ) r (lst ν) r' (toN π) (toN σ) : ℚ) := by
  have hg := h1.maps (tpow ν) r' (wt σ) (tpow σ) (tpow_mem_VE σ)
  rw [eq_sum_ptnsZ hg, op_sum_right hOp, coef_sum]
  unfold ClauseBound.Boson.mul2
  rw [sum_Pz, sum_toN]
  push_cast
  refine sum_congr rfl fun τ _ => ?_
  rw [coef_smul, coef_op_tpow hB hOp, coef_op_tpow hB hOp]
  ring
end GeneralPieces.LemQ
