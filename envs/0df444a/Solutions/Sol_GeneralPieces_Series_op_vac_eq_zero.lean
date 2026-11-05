-- Prove2me | solution 1 for GeneralPieces.Series.op_vac_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:08:44.118813+00:00
-- url     : https://prove2.me/submissions/25384c81-59f5-4de2-b203-eeb5acad9aa8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
import Theorems.Thm_GeneralPieces_Series_op_cons_vac
import Theorems.Thm_GeneralPieces_Series_bet_eq_zero
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
theorem _root_.solution (b : List ℕ) : ∀ {r : ℤ} (τ : Multiset ℕ), r < b.sum → op b r τ 0 = 0 := by
  induction b with
  | nil =>
    intro r τ h
    rw [op, if_neg (by simp at h; omega)]
    rfl
  | cons n b ih =>
    intro r τ h
    rw [op_cons_vac]
    refine sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l n with hl | hl
    · rw [bet_eq_zero hl, zero_mul]
    · rw [ih _ (by rw [List.sum_cons, Nat.cast_add] at h; omega), mul_zero]
end GeneralPieces.Series
