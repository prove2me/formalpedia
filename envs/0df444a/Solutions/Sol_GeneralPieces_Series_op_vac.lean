-- Prove2me | solution 1 for GeneralPieces.Series.op_vac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:09:45.867617+00:00
-- url     : https://prove2.me/submissions/5f5bc324-1590-4085-9b1c-fa616d91a73a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
import Theorems.Thm_GeneralPieces_Series_op_cons_vac
import Theorems.Thm_GeneralPieces_Series_bet_eq_zero
import Theorems.Thm_GeneralPieces_Series_bet_self
import Theorems.Thm_GeneralPieces_Series_op_vac_eq_zero
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
theorem _root_.solution {b : List ℕ} (hb : Pos b) : ∀ τ : Multiset ℕ, op b b.sum τ 0 = if τ = (b : Multiset ℕ) then 1 else 0 := by
  induction b with
  | nil =>
    intro τ
    rw [op, if_pos (by simp), one, Multiset.coe_nil]
  | cons n b ih =>
    intro τ
    have hn : 1 ≤ n := hb n List.mem_cons_self
    have hb' : Pos b := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hterm : ∀ l ∈ τ.toFinset, l ≠ n → bet n l * op b (((n :: b).sum : ℕ) - (l : ℤ)) (τ.erase l) 0 = 0 := by
      intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [bet_eq_zero h, zero_mul]
      · rw [op_vac_eq_zero b _ (by rw [List.sum_cons]; push_cast; omega), mul_zero]
    rw [op_cons_vac]
    by_cases hmem : n ∈ τ
    · rw [sum_eq_single_of_mem n (Multiset.mem_toFinset.2 hmem) hterm, bet_self hn, one_mul,
        show (((n :: b).sum : ℕ) : ℤ) - n = (b.sum : ℕ) by rw [List.sum_cons]; push_cast; ring, ih hb']
      refine if_congr ?_ rfl rfl
      rw [← Multiset.cons_coe]
      constructor
      · intro h
        rw [← h, Multiset.cons_erase hmem]
      · intro h
        rw [h, Multiset.erase_cons_head]
    · rw [sum_eq_zero fun l hl => hterm l hl fun h => hmem (h ▸ Multiset.mem_toFinset.1 hl), if_neg]
      intro h
      exact hmem (by rw [h, ← Multiset.cons_coe]; exact Multiset.mem_cons_self _ _)
end GeneralPieces.Series
