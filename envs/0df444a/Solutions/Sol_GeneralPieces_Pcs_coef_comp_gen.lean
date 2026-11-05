-- Prove2me | solution 1 for GeneralPieces.Pcs.coef_comp_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:27:02.805687+00:00
-- url     : https://prove2.me/submissions/54b8efa1-58cd-4eb8-8333-a8e3d33a383b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_LemQ_coef_sum
import Theorems.Thm_GeneralPieces_LemQ_eq_sum_ptnsZ
import Theorems.Thm_GeneralPieces_LemQ_op_sum_right
import Theorems.Thm_GeneralPieces_Ring_coef_smul


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (hOp : OpFacts) (h1 : O1) (a b : V) (r r' : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) (π : Ptn) :
    coef π (op a r (op b r' f)) = ∑ σ ∈ ptnsZ (E + r'), coef π (op a r (tpow σ)) * coef σ (op b r' f) := by
  have hg := h1.maps b r' E f hf
  conv_lhs => rw [eq_sum_ptnsZ hg, op_sum_right hOp, coef_sum]
  exact sum_congr rfl fun σ _ => by rw [coef_smul, mul_comm]
end GeneralPieces.Pcs
