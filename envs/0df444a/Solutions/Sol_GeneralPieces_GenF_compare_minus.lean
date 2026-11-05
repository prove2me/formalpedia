-- Prove2me | solution 1 for GeneralPieces.GenF.compare_minus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:09:28.653464+00:00
-- url     : https://prove2.me/submissions/e951b4a5-1202-4439-baf1-ebb6896086de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
import Theorems.Thm_GeneralPieces_GenF_ex_true
import Theorems.Thm_GeneralPieces_GenF_fM_eq_fP
import Theorems.Thm_GeneralPieces_GenF_coeff_expW_kap_true


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (h15 : StTwoOrders) (hY : StY) {a b : List ℕ} (ha : Pos a) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hw : π.sum = σ.sum)
    {E : ℕ} (hE : π.sum ≤ E) : fM a b π σ = fac (ex a b) • ∑ p ∈ antidiagonal (ex a b), (gam p.1 • epsM ^ wtX p.1) * coeff p.2 (normal true E π σ) := by
  rw [fM_eq_fP, ← hY true E b a π σ hb ha hπ hσ hw hE, ex_true, h15, coeff_mul]
  simp_rw [coeff_expW_kap_true]
end GeneralPieces.GenF
