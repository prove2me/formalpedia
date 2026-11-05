-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_aFam_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:33:18.692862+00:00
-- url     : https://prove2.me/submissions/570853c3-8d46-41c8-a1b3-e87ba7b72114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_nonneg
import Theorems.Thm_GeneralPieces_Sizes_l1_smul
import Theorems.Thm_GeneralPieces_Sizes_l1_monomial_le
import Theorems.Thm_GeneralPieces_Sizes_l1_mul_le
import Theorems.Thm_GeneralPieces_Sizes_l1_y_le
import Theorems.Thm_GeneralPieces_Sizes_wt_cons
import Theorems.Thm_ClauseBound_Boson_Text_wt_cons
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (μ : Ptn) : l1 (aFam μ) ≤ 2 ^ wt μ := by
  induction μ using Multiset.induction_on with
  | empty =>
    have : aFam 0 = monomial 0 1 := by simp [aFam]
    rw [this]
    exact (l1_monomial_le _ _).trans (by simp [wt])
  | cons n μ ih =>
    have e : aFam (n ::ₘ μ) = ((-1 : ℚ) ^ ((n : ℕ) - 1) • y n) * aFam μ := by
      unfold aFam
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [e, wt_cons, pow_add]
    refine (l1_mul_le _ _).trans (mul_le_mul ?_ ih (l1_nonneg _) (by positivity))
    rw [l1_smul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact l1_y_le n
end GeneralPieces.Sizes
