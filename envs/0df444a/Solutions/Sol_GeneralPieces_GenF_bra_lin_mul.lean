-- Prove2me | solution 1 for GeneralPieces.GenF.bra_lin_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:50:15.014498+00:00
-- url     : https://prove2.me/submissions/1975ddc2-449c-4f6f-8363-71dbceeffd8a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_support_bra
import Theorems.Thm_GeneralPieces_GenF_coeff_mul_big
import Theorems.Thm_GeneralPieces_GenF_toFinsupp_erase
import Theorems.Thm_GeneralPieces_GenF_coeff_linear_mul
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
theorem _root_.solution {g : Tv} (hg : Lin1 g) (σ : Multiset ℕ) (f : Tv) : bra σ (g * f) = ∑ l ∈ σ.toFinset, bra {l} g * bra (σ.erase l) f := by
  ext y : 2
  rw [coeff_bra, HahnSeries.coeff_mul, MvPolynomial.coeff_sum, HahnSeries.coeff_sum]
  simp only [coeff_mul_big _ _ g.isPWO_support f.isPWO_support (support_bra _ g) (support_bra _ f), coeff_linear_mul (hg _), Multiset.toFinsupp_support]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ij _ => ?_
  rw [coeff_bra, coeff_bra, Multiset.toFinsupp_singleton, toFinsupp_erase]
end GeneralPieces.GenF
