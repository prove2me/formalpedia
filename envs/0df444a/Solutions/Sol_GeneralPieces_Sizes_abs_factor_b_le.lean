-- Prove2me | solution 1 for GeneralPieces.Sizes.abs_factor_b_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:34:38.742363+00:00
-- url     : https://prove2.me/submissions/2b6b00e0-82fa-43f2-859f-8143c03a6fb6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_bFam_le
import Theorems.Thm_GeneralPieces_Sizes_abs_coef_op_le
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) {ν : Ptn} (hν : wt ν = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (op (bFam ν) r (tpow σ))| ≤ h.factorial * 2 ^ (12 * h ^ 2) := by
  refine (abs_coef_op_le hh (fun m hm => ?_) r h1 h2).trans (mul_le_mul_of_nonneg_right (hν ▸ l1_bFam_le ν) (by positivity))
  have h3 : m = Multiset.toFinsupp ν := by
    by_contra h0
    refine (mem_support_iff.1 hm) ?_
    unfold bFam tpow
    rw [coeff_smul, coeff_monomial, if_neg (Ne.symm h0), smul_zero]
  rw [h3, weight_toFinsupp, hν]
end GeneralPieces.Sizes
