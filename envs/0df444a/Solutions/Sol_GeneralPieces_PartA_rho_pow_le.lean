-- Prove2me | solution 1 for GeneralPieces.PartA.rho_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:32:31.590879+00:00
-- url     : https://prove2.me/submissions/c6c0a13c-6bfa-450f-9b6d-c08de359ae92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_logK_eq_x
import Theorems.Thm_GeneralPieces_PartA_rho_pow_eq
import Theorems.Thm_GeneralPieces_PartA_two_pow_ge

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (ρ : ℝ) (x₀ l : ℕ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hx : 1 ≤ x₀) :
    ρ ^ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ Real.logb 2 (1 / ρ) := by
  have hα : 0 ≤ Real.logb 2 (1 / ρ) := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hρ]; linarith)
  have hxpos : (0 : ℝ) < x x₀ l := by
    have h1 := x_ge_pow x₀ l
    have h2 : 0 < 2 ^ l * x₀ := by positivity
    exact_mod_cast lt_of_lt_of_le h2 h1
  rw [rho_pow_eq ρ l hρ, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), logK_eq_x]
  apply Real.rpow_le_rpow (by positivity) _ hα
  have h := two_pow_ge x₀ l
  rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
  exact h
end GeneralPieces.PartA
