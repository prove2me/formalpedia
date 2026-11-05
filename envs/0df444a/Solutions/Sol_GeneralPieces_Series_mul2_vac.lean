-- Prove2me | solution 1 for GeneralPieces.Series.mul2_vac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:11:03.201216+00:00
-- url     : https://prove2.me/submissions/846143b7-1538-488c-be9f-f97c1777539e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
import Theorems.Thm_GeneralPieces_Series_op_vac
import Theorems.Thm_ClauseBound_Boson_mem_Pz
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
theorem _root_.solution (a : List ℕ) {b : List ℕ} (hb : Pos b) : mul2 a (-(b.sum : ℤ)) b b.sum 0 0 = op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) := by
  rw [mul2, sum_eq_single_of_mem (b : Multiset ℕ)]
  · rw [op_vac hb, if_pos rfl, mul_one]
  · rw [mem_Pz]
    refine ⟨by simp, fun h => ?_⟩
    have := hb 0 (by simpa using h)
    omega
  · intro τ _ hτ
    rw [op_vac hb, if_neg hτ, mul_zero]
end GeneralPieces.Series
