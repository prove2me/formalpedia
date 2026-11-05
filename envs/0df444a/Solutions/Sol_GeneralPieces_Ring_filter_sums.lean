-- Prove2me | solution 1 for GeneralPieces.Ring.filter_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:29:55.54656+00:00
-- url     : https://prove2.me/submissions/ea570ec5-eab9-410f-afb6-571b34352f72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (ks : List ℤ) : (ks.filter (· < 0)).sum ≤ 0 ∧ 0 ≤ (ks.filter (0 < ·)).sum ∧ ks.sum = (ks.filter (· < 0)).sum + (ks.filter (0 < ·)).sum ∧
    ∀ k ∈ ks, (ks.filter (· < 0)).sum ≤ k ∧ k ≤ (ks.filter (0 < ·)).sum := by
  induction ks with
  | nil => simp
  | cons x ks ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [List.filter_cons_of_pos (by simpa using hx), List.filter_cons_of_neg (by simp; omega), List.sum_cons, List.sum_cons]
      refine ⟨by omega, h2, by omega, fun k hk => ?_⟩
      rcases List.mem_cons.1 hk with rfl | hk
      · omega
      · have := h4 k hk; omega
    · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_neg (by simp; omega), List.sum_cons]
      refine ⟨h1, h2, by omega, fun k hk => ?_⟩
      rcases List.mem_cons.1 hk with rfl | hk
      · omega
      · exact h4 k hk
    · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_pos (by simpa using hx), List.sum_cons, List.sum_cons]
      refine ⟨h1, by omega, by omega, fun k hk => ?_⟩
      rcases List.mem_cons.1 hk with rfl | hk
      · omega
      · have := h4 k hk; omega
end GeneralPieces.Ring
