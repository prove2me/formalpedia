-- Prove2me | solution 1 for GeneralPieces.GenF.Y2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:03:41.392887+00:00
-- url     : https://prove2.me/submissions/28e3c88c-968c-430b-b18e-c706f5e33d40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Theorems.Thm_GeneralPieces_GenF_y0_cons
import Theorems.Thm_GeneralPieces_GenF_pderiv_GG_xi
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_GG
import Theorems.Thm_GeneralPieces_GenF_sum_erase_le_sum
import Theorems.Thm_GeneralPieces_GenF_coeff_smul_mo_mul
import Theorems.Thm_GeneralPieces_GenF_pdL_C_mul
import Theorems.Thm_GeneralPieces_GenF_pdL_add
import Theorems.Thm_GeneralPieces_GenF_pdL_cons
import Theorems.Thm_GeneralPieces_GenF_pdL_nil
import Theorems.Thm_GeneralPieces_GenF_pdL_sum
import Theorems.Thm_GeneralPieces_GenF_pderiv_mapE
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
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (E : ℕ) (a : List ℕ) : Pos a → ∀ (σ : Multiset ℕ) (w : W), σ.sum ≤ E → (∀ n, MvPowerSeries.pderiv Tv (xi rd n) w = 0) →
    MvPowerSeries.constantCoeff (pdL (a.map (xi rd)) (GG rd E σ w)) = (MvPowerSeries.constantCoeff w).map (y0 a σ) := by
  induction a with
  | nil =>
    intro _ σ w _ _
    rw [List.map_nil, pdL_nil, constantCoeff_GG]
    rfl
  | cons n a ih =>
    intro ha σ w hσ hw
    have ha' : Pos a := fun m hm => ha m (List.mem_cons_of_mem _ hm)
    have hw' : ∀ m, MvPowerSeries.pderiv Tv (xi rd m) (mapD (JmT n) w) = 0 := fun m => by
      rw [mapD, pderiv_mapE (A := Tv) (JmT n).toLinearMap (xi rd m) w, hw m, map_zero]
    rw [List.map_cons, pdL_cons, pderiv_GG_xi rd hσ (ha n List.mem_cons_self) (hw n), pdL_add, pdL_sum, map_add, map_sum, ih ha' σ _ hσ hw',
      sum_congr rfl fun l _ => by rw [pdL_C_mul, map_mul, MvPowerSeries.constantCoeff_C, ih ha' (σ.erase l) w ((sum_erase_le_sum σ l).trans hσ) hw]]
    ext y : 2
    rw [HahnSeries.coeff_add, HahnSeries.coeff_sum]
    simp only [coeff_smul_mo_mul]
    show _ = y0 (n :: a) σ ((MvPowerSeries.constantCoeff w).coeff y)
    rw [y0_cons]
    rfl
end GeneralPieces.GenF
