-- Prove2me | solution 1 for GeneralPieces.GenF.bra_single_JpU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:50:32.324968+00:00
-- url     : https://prove2.me/submissions/d261fcf7-2590-4369-a662-2e0e5680eae6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_coeff_single_X
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
theorem _root_.solution {E l : ℕ} (hl : l ≤ E) (n : ℕ) : bra {l} (HahnSeries.C (JpU E n)) = (bet n l : ℚ) • mo ((l : ℤ) - n) 0 := by
  ext y : 2
  rw [coeff_bra, HahnSeries.C_apply, HahnSeries.coeff_single, coeff_smul_mo, Multiset.toFinsupp_singleton]
  by_cases hy : y = 0
  · rw [if_pos hy, if_pos hy]
    unfold JpU
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_C_mul, coeff_single_X, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · have h0 : l = 0 := by
        by_contra hne
        exact hm (Finset.mem_Icc.2 ⟨by omega, hl⟩)
      rw [h0]
      simp [bet]
  · rw [if_neg hy, if_neg hy, MvPolynomial.coeff_zero]
end GeneralPieces.GenF
