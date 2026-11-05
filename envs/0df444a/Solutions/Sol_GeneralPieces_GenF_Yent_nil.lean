-- Prove2me | solution 1 for GeneralPieces.GenF.Yent_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:58:20.341048+00:00
-- url     : https://prove2.me/submissions/04ed6b6e-27c6-44df-b1d6-0f619d468515

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
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
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
variable {R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (e : ℤ → R) (h0 : e 0 = 1) (τ σ : Multiset ℕ) : Yent e [] τ σ = if τ = σ then 1 else 0 := by
  unfold Yent
  by_cases h : τ = σ
  · subst h
    simp [op, one, h0]
  · rw [if_neg h]
    have : op [] ((τ.sum : ℤ) - σ.sum) τ σ = 0 := by
      unfold op
      split_ifs
      · exact if_neg h
      · rfl
    rw [this, Int.cast_zero, zero_smul]
end GeneralPieces.GenF
