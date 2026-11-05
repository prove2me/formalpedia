-- Prove2me | solution 1 for GeneralPieces.Ring.opMon_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:17.170029+00:00
-- url     : https://prove2.me/submissions/132f6783-477f-4b0f-b918-f125e3c47bcc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_exists_window
import Theorems.Thm_GeneralPieces_Ring_nordQ_nil
import Theorems.Thm_GeneralPieces_Ring_opMon_eq_opWin
import Theorems.Thm_GeneralPieces_Ring_term_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (r : ℤ) (f : V) : opMon [] r f = if r = 0 then f else 0 := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin hE [] h1 h2]
  unfold opWin
  rw [sum_filter]
  simp only [List.length_nil, ClauseBound.Boson.tup, sum_singleton]
  have ht : term [] [] f = f := by rw [term_eq, nordQ_nil]; simp [wtQ]
  by_cases hr : r = 0
  · rw [if_pos hr, if_pos (by rw [List.sum_nil]; omega), ht]
  · rw [if_neg hr, if_neg (by rw [List.sum_nil]; omega)]
end GeneralPieces.Ring
