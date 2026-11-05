-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_rhs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:54:09.011066+00:00
-- url     : https://prove2.me/submissions/ac0f76e4-6a9e-4a68-9ed9-4e5c65cc189f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
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
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) (i : X) (γ : X →₀ ℕ) :
    MvPowerSeries.coeff γ (∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i l) * normal rd E (σ.erase l) σ' +
      ∑ k ∈ σ'.toFinset, MvPowerSeries.C (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * normal rd E σ (σ'.erase k)) =
    ∑ l ∈ σ.toFinset, cS rd i l * MvPowerSeries.coeff γ (normal rd E (σ.erase l) σ') +
      ∑ k ∈ σ'.toFinset, (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * MvPowerSeries.coeff γ (normal rd E σ (σ'.erase k)) := by
  rw [map_add, map_sum, map_sum]
  simp only [MvPowerSeries.coeff_C_mul]
end GeneralPieces.GenF
