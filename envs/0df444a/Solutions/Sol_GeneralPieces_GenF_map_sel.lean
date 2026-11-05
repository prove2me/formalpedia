-- Prove2me | solution 1 for GeneralPieces.GenF.map_sel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:47:49.149222+00:00
-- url     : https://prove2.me/submissions/76175bcd-245e-4feb-838c-21a7b9b73f7b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
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
theorem _root_.solution {R R' : Type} [Zero R] [Zero R'] (φ : R → R') (h0 : φ 0 = 0) (rd : Bool) (f g : ℕ → R) (x : X) :
    φ (sel rd f g x) = sel rd (fun n => φ (f n)) (fun n => φ (g n)) x := by
  cases rd <;> rcases x with n | n <;> by_cases hn : n = 0 <;> simp [sel, z0, hn, h0]
end GeneralPieces.GenF
