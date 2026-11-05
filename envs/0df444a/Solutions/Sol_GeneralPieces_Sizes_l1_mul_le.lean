-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:32:01.977528+00:00
-- url     : https://prove2.me/submissions/c36d292b-e468-4d9a-b5a3-dd2ecde288d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_sum_le
import Theorems.Thm_GeneralPieces_Sizes_l1_monomial_le

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (a b : V) : l1 (a * b) ≤ l1 a * l1 b := by
  have e : a * b = ∑ m ∈ a.support, ∑ m' ∈ b.support, monomial (m + m') (coeff m a * coeff m' b) := by
    conv_lhs => rw [← support_sum_monomial_coeff a, ← support_sum_monomial_coeff b]
    rw [sum_mul_sum]
    simp_rw [monomial_mul]
  calc l1 (a * b) ≤ ∑ m ∈ a.support, ∑ m' ∈ b.support, |coeff m a| * |coeff m' b| := by
        rw [e]
        exact (l1_sum_le _ _).trans (sum_le_sum fun m _ => (l1_sum_le _ _).trans (sum_le_sum fun m' _ => (l1_monomial_le _ _).trans_eq (abs_mul _ _)))
    _ = l1 a * l1 b := by rw [l1, l1, sum_mul_sum]
end GeneralPieces.Sizes
