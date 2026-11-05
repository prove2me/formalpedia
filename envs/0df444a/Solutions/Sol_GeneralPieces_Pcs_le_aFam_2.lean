-- Prove2me | solution 2 for GeneralPieces.Pcs.le_aFam
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:34:31.588335+00:00
-- url     : https://prove2.me/submissions/ad97e814-3a3b-480a-ab0a-cc39f59d0e4b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_Le_smul
import Theorems.Thm_GeneralPieces_Pcs_le_tpow
import Theorems.Thm_GeneralPieces_Pcs_Le_mul
import Theorems.Thm_GeneralPieces_Pcs_one_eq_tpow
import Theorems.Thm_GeneralPieces_Pcs_wt_cons
import Theorems.Thm_GeneralPieces_Pcs_le_y
import Theorems.Thm_GeneralPieces_Pcs_aFam_zero
import Theorems.Thm_GeneralPieces_Pcs_aFam_cons
import Theorems.Thm_ClauseBound_Boson_Text_wt_cons
import Theorems.Thm_GeneralPieces_LemQ_Tri_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem solution (μ : Ptn) : Le (wt μ) (aFam μ) := by
  induction μ using Multiset.induction_on with
  | empty =>
    rw [aFam_zero, one_eq_tpow]
    exact le_tpow le_rfl
  | cons n μ ih =>
    rw [aFam_cons, wt_cons]
    exact ((le_y n).smul _).mul ih
