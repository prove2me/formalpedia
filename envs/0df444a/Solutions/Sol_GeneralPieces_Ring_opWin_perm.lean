-- Prove2me | solution 1 for GeneralPieces.Ring.opWin_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:40:13.535507+00:00
-- url     : https://prove2.me/submissions/2a8ee910-bcf0-441c-93c6-63fb0144490d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_P2M_GeneralPieces_Ring_sum_tup_succ__ab6e7a7dfbc1
import Theorems.Thm_GeneralPieces_Ring_opWin_cons
import Theorems.Thm_GeneralPieces_Ring_term_swap

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {μ μ' : List ℕ+} (h : μ.Perm μ') : ∀ (M : ℕ) (r : ℤ) (f : V), opWin μ M r f = opWin μ' M r f := by
  induction h with
  | nil => intro M r f; rfl
  | cons x _ ih =>
    intro M r f
    rw [opWin_cons, opWin_cons]
    simp only [ih]
  | swap x y μ =>
    intro M r f
    unfold opWin
    rw [sum_filter, sum_filter, List.length_cons, List.length_cons, List.length_cons, List.length_cons, sum_tup_succ', sum_tup_succ']
    simp only [sum_tup_succ']
    rw [sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun k' _ => sum_congr rfl fun ks _ => ?_
    have hc : (k' :: k :: ks).sum = -r ↔ (k :: k' :: ks).sum = -r := by
      simp only [List.sum_cons]; constructor <;> intro h <;> omega
    rw [if_congr hc rfl rfl, term_swap]
  | trans _ _ ih1 ih2 => intro M r f; rw [ih1, ih2]
end GeneralPieces.Ring
