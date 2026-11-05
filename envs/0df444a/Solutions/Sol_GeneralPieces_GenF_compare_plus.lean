-- Prove2me | solution 1 for GeneralPieces.GenF.compare_plus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:08:48.759396+00:00
-- url     : https://prove2.me/submissions/b2b25fcf-3134-4c35-91cb-3a710478ae89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
import Theorems.Thm_GeneralPieces_GenF_ex_false
import Theorems.Thm_GeneralPieces_GenF_coeff_expW_kap_false


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (h15 : StTwoOrders) (hY : StY) {a b : List ℕ} (ha : Pos a) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hw : π.sum = σ.sum)
    {E : ℕ} (hE : π.sum ≤ E) : fP a b π σ = fac (ex a b) • ∑ p ∈ antidiagonal (ex a b), (gam p.1 • epsP ^ wtX p.1) * coeff p.2 (normal false E π σ) := by
  rw [← hY false E a b π σ ha hb hπ hσ hw hE, ex_false, h15, coeff_mul]
  simp_rw [coeff_expW_kap_false]
end GeneralPieces.GenF
