-- Prove2me | solution 2 for GeneralPieces.Sizes.l1_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:29:33.29914+00:00
-- url     : https://prove2.me/submissions/d607580c-3d9d-4b18-9f0e-0adf8fde3caa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_eq_sum

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (a b : V) : l1 (a + b) ≤ l1 a + l1 b := by
  classical
  rw [l1_eq_sum (support_add (p := a) (q := b)), l1_eq_sum (a := a) (subset_union_left (s₂ := b.support)),
    l1_eq_sum (a := b) (subset_union_right (s₁ := a.support)), ← sum_add_distrib]
  exact sum_le_sum fun m _ => by rw [coeff_add]; exact abs_add_le _ _
end GeneralPieces.Sizes
