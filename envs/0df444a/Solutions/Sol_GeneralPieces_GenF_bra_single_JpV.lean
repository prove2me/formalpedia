-- Prove2me | solution 1 for GeneralPieces.GenF.bra_single_JpV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:51:00.88748+00:00
-- url     : https://prove2.me/submissions/6155b130-4e84-42f7-a268-28945cdcc454

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_coeff_single_X
import Theorems.Thm_GeneralPieces_GenF_bet_eq_zero_of_lt
import Theorems.Thm_GeneralPieces_GenF_coeff_JpV
import Theorems.Thm_GeneralPieces_GenF_coeff_smul_mo
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (l n : ℕ) : bra {l} (JpV n) = (bet n l : ℚ) • mo 0 ((l : ℤ) - n) := by
  ext y : 2
  rw [coeff_bra, coeff_JpV, coeff_smul_mo, Multiset.toFinsupp_singleton, T_zero, mul_one]
  by_cases hy : 0 ≤ y
  · rw [if_pos hy, MvPolynomial.coeff_C_mul, coeff_single_X]
    by_cases e : l = (y + n).toNat
    · rw [if_pos e, if_pos (by omega), mul_one, show y + (n : ℤ) = (l : ℤ) by omega]
    · rw [if_neg e, if_neg (by omega), mul_zero]
  · rw [if_neg hy, MvPolynomial.coeff_zero]
    split_ifs with e
    · rw [bet_eq_zero_of_lt (by omega)]
      simp
    · rfl
end GeneralPieces.GenF
