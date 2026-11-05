-- Prove2me | solution 1 for GeneralPieces.PartA.y_le_exp_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:32:38.350717+00:00
-- url     : https://prove2.me/submissions/f78aa323-bab8-4a9d-97a1-155b18478f66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_y_zero
import Theorems.Thm_P2M_GeneralPieces_PartA_y_succ_le__934cf0d43d5c
import Theorems.Thm_GeneralPieces_PartA_le_exp_sum_mul
import Theorems.Thm_GeneralPieces_PartA_hasSum_a
import Theorems.Thm_GeneralPieces_PartA_hasSum_b

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) :
    y ρ x₀ l ≤ Real.exp (∑' j : ℕ, (1 : ℝ) / 2 ^ (j + 2)) * (1 / 2 + ∑' j : ℕ, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) := by
  have h := le_exp_sum_mul (y ρ x₀) (fun j => 1 / 2 ^ (j + 2)) (fun j => 6 * 2 ^ j / 2 ^ (18 * (j + 1)))
    (fun j => by positivity) (fun j => by positivity) (by rw [y_zero]; norm_num)
    (fun l => y_succ_le' ρ x₀ l hρ hx) l
  rw [y_zero] at h
  have ha : ∑ j ∈ range l, (1 : ℝ) / 2 ^ (j + 2) ≤ ∑' j : ℕ, (1 : ℝ) / 2 ^ (j + 2) :=
    hasSum_a.summable.sum_le_tsum _ (fun j _ => by positivity)
  have hb : ∑ j ∈ range l, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1)) ≤ ∑' j : ℕ, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1)) :=
    hasSum_b.summable.sum_le_tsum _ (fun j _ => by positivity)
  refine le_trans h (mul_le_mul (Real.exp_le_exp.mpr ha) (by linarith) ?_ (Real.exp_pos _).le)
  exact add_nonneg (by norm_num) (sum_nonneg fun j _ => by positivity)
end GeneralPieces.PartA
