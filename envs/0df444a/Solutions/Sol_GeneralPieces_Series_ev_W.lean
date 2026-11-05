-- Prove2me | solution 1 for GeneralPieces.Series.ev_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:11.102281+00:00
-- url     : https://prove2.me/submissions/97ec8185-7efc-4b52-a960-04e25d605115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
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
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
theorem _root_.solution (x y : ℤ) : ev (W x y) = 1 := by
  rw [ev, W, AddMonoidAlgebra.lift_single]
  simp
end GeneralPieces.Series
