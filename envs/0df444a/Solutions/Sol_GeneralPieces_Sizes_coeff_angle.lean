-- Prove2me | solution 1 for GeneralPieces.Sizes.coeff_angle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:27:59.608682+00:00
-- url     : https://prove2.me/submissions/462eead9-8b5d-4409-80f2-4947c8e4c792

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (h i : ℕ) (a : V) (m : ℕ+ →₀ ℕ) :
    coeff m (angle h i a) = if Finsupp.weight wgt m ≤ h then ((Finsupp.weight wgt m + h).choose i : ℚ) * coeff m a else 0 := by
  unfold angle part
  rw [coeff_sum]
  simp_rw [coeff_smul, coeff_weightedHomogeneousComponent, smul_eq_mul, mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]
  rfl
end GeneralPieces.Sizes
