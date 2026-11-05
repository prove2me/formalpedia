-- Prove2me | solution 1 for GeneralPieces.GenF.Phi_Bp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:56:09.222043+00:00
-- url     : https://prove2.me/submissions/8a2806d5-9644-4d24-a83c-50b6da5a6b0c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
import Theorems.Thm_GeneralPieces_GenF_DD_sel
import Theorems.Thm_GeneralPieces_GenF_DD_emb
import Theorems.Thm_GeneralPieces_GenF_dsum_Bp
import Theorems.Thm_GeneralPieces_GenF_expD_of_sq_zero
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
theorem _root_.solution (rd : Bool) : Phi rd (Bp rd) = Bp rd + embW (kap rd) := by
  have h : ∀ (i j : X) (α : X →₀ ℕ), DD rd i (DD rd j (coeff α (Bp rd))) = 0 := by
    intro i j α
    have hlin : coeff α (Bp rd) = if α.degree = 1 then ∑ v ∈ α.support, sel rd 0 JpV v else 0 := rfl
    rw [hlin]
    split_ifs
    · rw [map_sum]
      simp only [DD_sel]
      rw [← map_sum, DD_emb]
    · simp
  have h1 := expD_of_sq_zero (X := X) (A := Tv) (w := Bp rd) (DD rd) h
  rw [dsum_Bp] at h1
  exact h1
end GeneralPieces.GenF
