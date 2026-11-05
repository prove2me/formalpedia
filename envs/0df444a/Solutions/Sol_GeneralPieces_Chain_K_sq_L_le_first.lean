-- Prove2me | solution 1 for GeneralPieces.Chain.K_sq_L_le_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:53.517614+00:00
-- url     : https://prove2.me/submissions/fe36fe37-d570-4784-a9c5-a12061db9cce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_ClauseBound_Gen_K_cast
import Theorems.Thm_ClauseBound_Gen_Rate_step_D__34894c
import Theorems.Thm_ClauseBound_Gen_Rate_step_K
import Theorems.Thm_ClauseBound_Gen_Rate_step_d
import Theorems.Thm_ClauseBound_Gen_Rate_step_p
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (hm : P.m = 1) (x₀ l lam : ℕ) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤
      ubarG P (step P x₀ l) lam + 2 * zeta l * ((g x₀ l : ℝ) ^ 4 * lam) + (K x₀ l : ℝ) ^ 2 := by
  have hK : (0 : ℝ) < K x₀ l := by rw [K_cast]; positivity
  have hdiv := Nat.cast_div_le (α := ℝ)
    (m := (step P x₀ l).D * ubarG P (step P x₀ l) lam + 3 * (step P x₀ l).p ^ 2 * ((step P x₀ l).d ^ 2 * (P.m * lam)))
    (n := (step P x₀ l).D * (step P x₀ l).K ^ 2)
  have e : (2 : ℝ) * zeta l = 1 / 2 ^ (l + 4) := by
    rw [zeta, pow_succ (2 : ℝ) (l + 4)]; field_simp
  rw [lamNextG, Nat.cast_add, Nat.cast_one, mul_add, mul_one, e]
  refine add_le_add_left ?_ _
  refine (mul_le_mul_of_nonneg_left hdiv (by positivity)).trans (le_of_eq ?_)
  rw [step_D, step_K, step_p, step_d, hm]
  push_cast
  field_simp
end GeneralPieces.Chain
