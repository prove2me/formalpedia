-- Prove2me | solution 1 for GeneralPieces.Sizes.abs_coef_op_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:33:23.982351+00:00
-- url     : https://prove2.me/submissions/d3f5f2ac-1428-42bc-a7af-8f8c3ef771a3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_P2M_GeneralPieces_Sizes_abs_entry_le__393226c38f88
import Theorems.Thm_GeneralPieces_Sizes_coef_op
import Theorems.Thm_GeneralPieces_Sizes_sum_toL_toList
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) {a : V} (ha : ∀ m ∈ a.support, Finsupp.weight wgt m ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h)
    (h2 : wt σ ≤ 4 * h) : |coef σ' (op a r (tpow σ))| ≤ l1 a * 2 ^ (12 * h ^ 2) := by
  rw [coef_op, l1, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_entry_le' hh _ (by rw [sum_toL_toList]; exact ha m hm) r h1 h2) (abs_nonneg _)
end GeneralPieces.Sizes
