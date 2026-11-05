-- Prove2me | solution 1 for GeneralPieces.GenF.op_eq_zero_of_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:00:44.375036+00:00
-- url     : https://prove2.me/submissions/f709f7a5-d061-4f93-a41d-949dc0cd503d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
namespace GeneralPieces.GenF
theorem _root_.solution (b : List ℕ) (r : ℤ) {τ σ : Multiset ℕ} (hτ : 0 ∈ τ) (hσ : 0 ∉ σ) : op b r τ σ = 0 := by
  induction b generalizing r τ σ with
  | nil =>
    unfold op
    split_ifs
    · exact if_neg fun h : τ = σ => hσ (h ▸ hτ)
    · rfl
  | cons n b ih =>
    rw [op, nop, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro k _
      rw [ann, ih _ hτ fun h => hσ (Multiset.mem_of_mem_erase h), mul_zero, mul_zero]
    · intro l hl
      by_cases h0 : l = 0
      · rw [h0, bet, if_pos Nat.cast_zero, zero_mul]
      · rw [cre, if_pos (Multiset.mem_toFinset.1 hl), ih _ ((Multiset.mem_erase_of_ne (Ne.symm h0)).2 hτ) hσ, mul_zero]
end GeneralPieces.GenF
