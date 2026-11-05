-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_angle_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:29:44.257998+00:00
-- url     : https://prove2.me/submissions/407a42a1-ff07-4108-8153-521072ac8ea9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_eq_sum
import Theorems.Thm_GeneralPieces_Sizes_coeff_angle

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (h i : ℕ) (a : V) : l1 (angle h i a) ≤ 2 ^ (2 * h) * l1 a := by
  have hS : (angle h i a).support ⊆ a.support := fun m hm => by
    rw [mem_support_iff, coeff_angle] at hm
    rw [mem_support_iff]
    intro h0
    rw [h0, mul_zero, ite_self] at hm
    exact hm rfl
  rw [l1_eq_sum hS, l1, mul_sum]
  refine sum_le_sum fun m _ => ?_
  rw [coeff_angle]
  split_ifs with hm
  · rw [abs_mul, Nat.abs_cast]
    have : (Finsupp.weight wgt m + h).choose i ≤ 2 ^ (2 * h) :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (abs_nonneg _)
  · rw [abs_zero]
    positivity
end GeneralPieces.Sizes
