-- Prove2me | solution 1 for GeneralPieces.GenF.sum_filter_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:08.429627+00:00
-- url     : https://prove2.me/submissions/60a163d5-0e32-41ea-8fd5-9d3b27d834f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
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
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution {ι : Type} (l : List ι) (F : ι → ℚ × ℕ × L) (H : ℕ) :
    (((l.map F).filter fun c => c.2.1 = H).map fun c => c.1).sum = (l.map fun x => if (F x).2.1 = H then (F x).1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.filter_cons, decide_eq_true_eq, List.sum_cons]
    split_ifs with h
    · rw [List.map_cons, List.sum_cons, ih]
    · rw [ih, zero_add]
end GeneralPieces.GenF
