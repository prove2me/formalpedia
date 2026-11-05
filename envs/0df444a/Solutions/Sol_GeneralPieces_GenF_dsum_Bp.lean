-- Prove2me | solution 1 for GeneralPieces.GenF.dsum_Bp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:54:42.608473+00:00
-- url     : https://prove2.me/submissions/d25e36a2-4a61-46d6-a753-2c8326e617d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
import Theorems.Thm_GeneralPieces_GenF_kap_eq
import Theorems.Thm_GeneralPieces_GenF_DD_sel
import Theorems.Thm_GeneralPieces_GenF_kq_self
import Theorems.Thm_GeneralPieces_GenF_coeff_bil
import Theorems.Thm_GeneralPieces_GenF_coeff_dsum
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
open MvPowerSeries hiding C X
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) : dsum (DD rd) (Bp rd) = embW (kap rd) := by
  refine MvPowerSeries.ext fun α => ?_
  have hL := coeff_dsum (X := X) (A := Tv) (DD rd) (Bp rd) α
  have hlin : ∀ β : X →₀ ℕ, coeff β (Bp rd) = if β.degree = 1 then ∑ v ∈ β.support, sel rd 0 JpV v else 0 := fun _ => rfl
  rw [hL, embW, coeff_map, kap_eq, coeff_bil]
  by_cases h2 : α.degree = 2
  · rw [if_pos h2, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hlin, if_pos (by have := degree_sub_single hi; omega), map_sum, map_sum]
    simp only [DD_sel]
    refine Finset.sum_subset Finsupp.support_tsub fun v hv hv' => ?_
    have hvi : v = i := by
      by_contra hne
      apply hv'
      rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_eq_of_ne hne, tsub_zero]
      exact Finsupp.mem_support_iff.1 hv
    rw [hvi, kq_self, map_zero]
  · rw [if_neg h2, map_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hlin, if_neg (by have := degree_sub_single hi; omega), map_zero]
end GeneralPieces.GenF
