-- Prove2me | solution 1 for GeneralPieces.GenF.DD_emb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:53:16.920382+00:00
-- url     : https://prove2.me/submissions/63ed8768-dcc0-4287-9435-5faf54ea89ef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
import Theorems.Thm_GeneralPieces_GenF_JmT_emb
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
open MvPowerSeries hiding C X
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (i : X) (s : S) : DD rd i (emb s) = 0 := by
  cases rd <;> rcases i with i | i <;> simp only [DD, sel, z0, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, if_true, Pi.zero_apply] <;> split_ifs <;> simp [JmT_emb]
end GeneralPieces.GenF
