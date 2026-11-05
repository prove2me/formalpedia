-- Prove2me | solution 1 for GeneralPieces.GenF.stN3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:55:05.938722+00:00
-- url     : https://prove2.me/submissions/dc72e461-62e4-45e9-864b-8726ef419ee2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
import Theorems.Thm_GeneralPieces_GenF_coeff_add_single
import Theorems.Thm_GeneralPieces_GenF_stN2
import Theorems.Thm_GeneralPieces_GenF_induction_single
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
theorem _root_.solution (hN : StNeq) : StN3 := by
  intro rd E
  ext γ : 1
  induction γ using induction_single with
  | h0 => rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, stN2, if_pos rfl, MvPowerSeries.coeff_zero_one]
  | hs γ i _ =>
    classical
    rw [coeff_add_single, hN rd E 0 0 i (by simp), MvPowerSeries.coeff_one, if_neg]
    · simp
    · intro h
      have := congrArg (fun m : X →₀ ℕ => m i) h
      simp at this
end GeneralPieces.GenF
