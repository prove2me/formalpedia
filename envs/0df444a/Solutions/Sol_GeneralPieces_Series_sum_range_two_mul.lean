-- Prove2me | solution 1 for GeneralPieces.Series.sum_range_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:20.709896+00:00
-- url     : https://prove2.me/submissions/1c37d653-d1d9-4eb5-bc1a-34d622334005

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
theorem _root_.solution {H h : ℕ} (hH : H ≤ 2 * h) (g : ℕ → ℤ) :
    ∑ i ∈ range (2 * h + 1), (-1) ^ i * (H.choose i : ℤ) * g i = ∑ i ∈ range (H + 1), (-1) ^ i * (H.choose i : ℤ) * g i := by
  refine (sum_subset (range_subset_range.2 (by omega)) fun i _ hi => ?_).symm
  rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range, not_lt] at hi; omega)]
  simp
end GeneralPieces.Series
