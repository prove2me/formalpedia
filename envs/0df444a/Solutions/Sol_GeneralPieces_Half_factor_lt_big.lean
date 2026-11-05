-- Prove2me | solution 1 for GeneralPieces.Half.factor_lt_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:15:27.383388+00:00
-- url     : https://prove2.me/submissions/56e60f0a-ee1e-4415-bef0-d9e645ac381e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_Half_Size
import Theorems.Thm_ClauseBound_Part_p_pos
import Theorems.Thm_GeneralPieces_ThmHalfPieces_bound_lt_big
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution (h : ℕ) : 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) < 2 ^ ClauseBound.Boson.big h ∧ h.factorial * 2 ^ (12 * h ^ 2) < 2 ^ ClauseBound.Boson.big h := by
  have h1 : 1 ≤ Delta h := (ClauseBound.Part.p_pos 0).trans (single_le_sum (f := Partitions.p) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))
  have h2 : 1 ≤ 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) := Nat.mul_pos (by positivity) (by positivity)
  have h3 : 1 ≤ h.factorial * 2 ^ (12 * h ^ 2) := Nat.mul_pos h.factorial_pos (by positivity)
  have h4 := ThmHalfPieces.bound_lt_big h
  generalize 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) = a at h2 h4 ⊢
  generalize h.factorial * 2 ^ (12 * h ^ 2) = b at h3 h4 ⊢
  have h5 : a ≤ a * b := Nat.le_mul_of_pos_right _ h3
  have h6 : b ≤ a * b := Nat.le_mul_of_pos_left _ h2
  have h7 : a * b ≤ Delta h * (a * b) := Nat.le_mul_of_pos_left _ h1
  exact ⟨(h5.trans h7).trans_lt h4, (h6.trans h7).trans_lt h4⟩
end GeneralPieces.Half
