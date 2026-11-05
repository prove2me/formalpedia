-- Prove2me | solution 1 for GeneralPieces.GenF.fP_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:49.192693+00:00
-- url     : https://prove2.me/submissions/20f998d6-75a3-478e-98c8-2b76c73eaa24

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
import Theorems.Thm_GeneralPieces_GenF_mul2_eq_zero_of_sum_ne
import Theorems.Thm_GeneralPieces_Series_cfP_fP
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Series_ext_cf
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (a b : List ℕ) {π σ : Multiset ℕ} (hne : π.sum ≠ σ.sum) : fP a b π σ = 0 := ext_cf fun x y => by
  have h := cfP_fP a b π σ x y
  rw [cfP] at h
  rw [h, cf_zero]
  split_ifs with h1
  · rw [mul2_eq_zero_of_sum_ne a b (by omega) hne, Int.cast_zero]
  · rfl
end GeneralPieces.GenF
