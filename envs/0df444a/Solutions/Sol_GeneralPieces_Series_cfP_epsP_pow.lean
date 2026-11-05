-- Prove2me | solution 1 for GeneralPieces.Series.cfP_epsP_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:09:06.549207+00:00
-- url     : https://prove2.me/submissions/85e20ed3-4b87-4a6d-bb34-8dbb9985a0ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_diag
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_one
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Series_eps_pow_succ
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ}
namespace GeneralPieces.Series
theorem _root_.solution (N : ℕ) : cfP (epsP ^ N) (-(N : ℤ)) 0 = 1 := by
  rw [cfP, epsP]
  rcases N with _ | N
  · rw [pow_zero, cf_one]
    simp
  · rw [eps_pow_succ, cf_diag, if_pos ⟨le_refl _, by push_cast; ring⟩]
    simp
end GeneralPieces.Series
