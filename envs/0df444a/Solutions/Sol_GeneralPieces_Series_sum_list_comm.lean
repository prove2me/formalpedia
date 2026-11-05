-- Prove2me | solution 1 for GeneralPieces.Series.sum_list_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:23.21443+00:00
-- url     : https://prove2.me/submissions/9e2bfc6f-67bc-48db-a0a9-4d3d2b98331a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
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
open ClauseBound.Boson Finset
namespace GeneralPieces.Series
theorem _root_.solution {ι α : Type} (s : Finset ι) (A : List α) (f : ι → α → ℤ) : ∑ i ∈ s, (A.map (f i)).sum = (A.map fun c => ∑ i ∈ s, f i c).sum := by
  induction A with
  | nil => simp
  | cons c A ih => simp only [List.map_cons, List.sum_cons, sum_add_distrib, ih]
end GeneralPieces.Series
