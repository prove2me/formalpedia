-- Prove2me | solution 2 for GeneralPieces.Sizes.l1_y_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:32:09.586743+00:00
-- url     : https://prove2.me/submissions/782a4d58-eb90-434b-ae29-9587491db900

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_sum_le
import Theorems.Thm_GeneralPieces_Sizes_l1_smul
import Theorems.Thm_GeneralPieces_Sizes_l1_monomial_le

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (n : ℕ+) : l1 (y n) ≤ 2 ^ (n : ℕ) := by
  have a1 : ∑ j ∈ Icc 1 (n : ℕ), (n : ℕ).choose j ≤ 2 ^ (n : ℕ) := by
    rw [← Nat.sum_range_choose]
    exact sum_le_sum_of_subset fun j hj => mem_range.2 (by have := (mem_Icc.1 hj).2; omega)
  calc l1 (y n) ≤ ∑ j ∈ Icc 1 (n : ℕ), (((n : ℕ).choose j : ℕ) : ℚ) := by
        refine (l1_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [l1_smul, Nat.abs_cast]
        have : l1 (X j.toPNat' : V) ≤ 1 := (l1_monomial_le _ _).trans_eq abs_one
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) this
    _ ≤ 2 ^ (n : ℕ) := by exact_mod_cast a1
end GeneralPieces.Sizes
