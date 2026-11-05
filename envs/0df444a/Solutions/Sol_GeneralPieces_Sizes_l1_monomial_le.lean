-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_monomial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:24:38.430118+00:00
-- url     : https://prove2.me/submissions/21310d5b-f712-4a96-b6f8-f1ba098676f2

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
theorem _root_.solution (m : ℕ+ →₀ ℕ) (q : ℚ) : l1 (monomial m q) ≤ |q| := by
  classical
  rw [l1_eq_sum (support_monomial_subset (s := m) (a := q)), sum_singleton, coeff_monomial, if_pos rfl]
end GeneralPieces.Sizes
