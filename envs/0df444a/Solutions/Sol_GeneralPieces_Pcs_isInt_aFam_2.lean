-- Prove2me | solution 2 for GeneralPieces.Pcs.isInt_aFam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:29:38.707004+00:00
-- url     : https://prove2.me/submissions/b880ee69-4017-4509-84bf-4a483eed432e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_one_eq_tpow
import Theorems.Thm_GeneralPieces_Pcs_aFam_zero
import Theorems.Thm_GeneralPieces_Pcs_aFam_cons
import Theorems.Thm_GeneralPieces_Pcs_isInt_smul
import Theorems.Thm_GeneralPieces_Pcs_isInt_mul
import Theorems.Thm_GeneralPieces_Pcs_isInt_tpow
import Theorems.Thm_GeneralPieces_Pcs_isInt_y

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (μ : Ptn) : IsInt (aFam μ) := by
  induction μ using Multiset.induction_on with
  | empty =>
    rw [aFam_zero, one_eq_tpow]
    exact isInt_tpow 0
  | cons n μ ih =>
    rw [aFam_cons]
    have := isInt_smul (isInt_y n) ((-1) ^ ((n : ℕ) - 1))
    push_cast at this
    exact isInt_mul this ih
end GeneralPieces.Pcs
