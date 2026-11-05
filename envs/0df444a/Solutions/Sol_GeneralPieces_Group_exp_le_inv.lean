-- Prove2me | solution 1 for GeneralPieces.Group.exp_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:22.58035+00:00
-- url     : https://prove2.me/submissions/d46230bf-56f9-4983-8ad5-2b36ea4849f3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (hK : 1 ≤ K) (hn : 1 ≤ n) {ζ : ℝ} (h : (K : ℝ) * Real.log (2 * ((K * n : ℕ) : ℝ) * K) ≤ 2 * ζ ^ 2 * ((K * n : ℕ) : ℝ)) :
    Real.exp (-(2 * n * ζ ^ 2)) ≤ 1 / (2 * ((K * n : ℕ) : ℝ) * K) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 2 * ((K * n : ℕ) : ℝ) * K := by push_cast; positivity
  have h1 : Real.log (2 * ((K * n : ℕ) : ℝ) * K) ≤ 2 * n * ζ ^ 2 := by
    refine le_of_mul_le_mul_left (h.trans (le_of_eq ?_)) hK0
    push_cast; ring
  rw [one_div, ← Real.exp_log hpos, ← Real.exp_neg, Real.exp_le_exp]
  linarith
end GeneralPieces.Group
