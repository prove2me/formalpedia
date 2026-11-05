-- Prove2me | solution 1 for GeneralPieces.Sizes.abs_factor_a_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:35:47.029565+00:00
-- url     : https://prove2.me/submissions/afc7f48e-59eb-4268-b690-6ed56e875f08

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_coeff_angle
import Theorems.Thm_GeneralPieces_Sizes_l1_angle_aFam_le
import Theorems.Thm_GeneralPieces_Sizes_abs_coef_op_le
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) (i : ℕ) {ξ : Ptn} (hξ : wt ξ = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (op (angle h i (aFam ξ)) r (tpow σ))| ≤ 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) := by
  refine (abs_coef_op_le hh (fun m hm => ?_) r h1 h2).trans (mul_le_mul_of_nonneg_right (l1_angle_aFam_le i hξ) (by positivity))
  rw [mem_support_iff, coeff_angle] at hm
  by_contra h0
  exact hm (if_neg h0)
end GeneralPieces.Sizes
