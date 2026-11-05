-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:25:53.035078+00:00
-- url     : https://prove2.me/submissions/563cfed5-db61-4ce7-8aa8-7855590cde2b

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
theorem _root_.solution (q : ℚ) (a : V) : l1 (q • a) = |q| * l1 a := by
  rw [l1_eq_sum (support_smul (a := q) (f := a)), l1, mul_sum]
  exact sum_congr rfl fun m _ => by rw [coeff_smul, smul_eq_mul, abs_mul]
end GeneralPieces.Sizes
