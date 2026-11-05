-- Prove2me | solution 1 for GeneralPieces.GenF.braW_C_sel_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:56:46.364369+00:00
-- url     : https://prove2.me/submissions/e4753bca-f84e-47da-80eb-0ae453ecc098

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_braW_C_JpU_mul
import Theorems.Thm_GeneralPieces_GenF_braW_C_JpV_mul
import Theorems.Thm_GeneralPieces_GenF_sel_xi
import Theorems.Thm_GeneralPieces_GenF_sel_xi_zero
import Theorems.Thm_GeneralPieces_GenF_sel_xo
import Theorems.Thm_GeneralPieces_GenF_sel_xo_zero
import Theorems.Thm_GeneralPieces_GenF_xi_or_xo
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
theorem _root_.solution (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) (i : X) (w : W) :
    braW σ (MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) JpV i) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i (l : ℤ)) * braW (σ.erase l) w := by
  rcases xi_or_xo rd i with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · by_cases hn : n = 0
    · subst hn
      simp only [cS, sel_xi_zero]
      simp [braW_zero]
    · simp only [cS, sel_xi rd _ _ (show 1 ≤ n by omega)]
      exact braW_C_JpU_mul hσ n w
  · by_cases hn : n = 0
    · subst hn
      simp only [cS, sel_xo_zero]
      simp [braW_zero]
    · simp only [cS, sel_xo rd _ _ (show 1 ≤ n by omega)]
      exact braW_C_JpV_mul σ n w
end GeneralPieces.GenF
