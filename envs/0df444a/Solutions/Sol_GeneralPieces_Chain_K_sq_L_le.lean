-- Prove2me | solution 1 for GeneralPieces.Chain.K_sq_L_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:39.441528+00:00
-- url     : https://prove2.me/submissions/bd909ae7-27dd-42f1-aa50-b1252f9b7ae6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_GeneralPieces_Chain_ubar_le_first
import Theorems.Thm_GeneralPieces_Chain_ubar_le_second
import Theorems.Thm_GeneralPieces_Chain_inv_g_le_zeta
import Theorems.Thm_GeneralPieces_Chain_K_sq_L_le_first
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (hP : Par P ρ c) (hm : P.m = 1) (x₀ l lam : ℕ) (hx : 18 ≤ x₀) (hlam : 1 ≤ lam) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤
      (ρ + 3 * zeta l) * ((g x₀ l : ℝ) ^ 4 * lam) + c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) + (K x₀ l : ℝ) ^ 2 := by
  have h1 := K_sq_L_le_first hm x₀ l lam
  have h2 := (ubar_le_first hP x₀ l lam hx hlam).trans (ubar_le_second hP x₀ l lam hlam)
  have h3 : (g x₀ l : ℝ) ^ 4 * lam * (1 / g x₀ l) ≤ (g x₀ l : ℝ) ^ 4 * lam * zeta l :=
    mul_le_mul_of_nonneg_left (inv_g_le_zeta x₀ l hx) (by positivity)
  linarith
end GeneralPieces.Chain
