-- Prove2me | solution 1 for GeneralPieces.Chain.ubar_le_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:18.240029+00:00
-- url     : https://prove2.me/submissions/a1155170-ec14-44cd-a68f-abbaf78c5afe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_GeneralPieces_Chain_ubar_eq
import Theorems.Thm_ClauseBound_Gen_Rate_pow_le_g


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (hP : Par P ρ c) (x₀ l lam : ℕ) (hx : 18 ≤ x₀) (hlam : 1 ≤ lam) :
    (ubarG P (step P x₀ l) lam : ℝ) ≤ (g x₀ l : ℝ) ^ 4 * lam / g x₀ l +
      nRectG (g x₀ l) (g x₀ l) * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) := by
  have hg : (0 : ℝ) < g x₀ l := by
    have := pow_le_g hx l
    exact_mod_cast lt_of_lt_of_le (by positivity) this
  have hs : ((g x₀ l * (g x₀ l - 1) * g x₀ l * lam : ℕ) : ℝ) ≤ (g x₀ l : ℝ) ^ 3 * lam := by
    have : g x₀ l * (g x₀ l - 1) * g x₀ l * lam ≤ g x₀ l ^ 3 * lam := by
      calc g x₀ l * (g x₀ l - 1) * g x₀ l * lam ≤ g x₀ l * g x₀ l * g x₀ l * lam := by gcongr; exact Nat.sub_le _ _
        _ = g x₀ l ^ 3 * lam := by ring
    exact_mod_cast this
  have e1 : (g x₀ l : ℝ) ^ 4 * lam / g x₀ l = (g x₀ l : ℝ) ^ 3 * lam := by field_simp
  rw [ubar_eq, e1, Nat.cast_add, Nat.cast_mul (nRectG _ _)]
  exact add_le_add hs (mul_le_mul_of_nonneg_left (hP.caps 0 lam hlam) (Nat.cast_nonneg _))
end GeneralPieces.Chain
