-- Prove2me | solution 1 for GeneralPieces.Rate.st_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:18.813782+00:00
-- url     : https://prove2.me/submissions/cae0963b-db0a-45cb-8e62-ea790f5e1906

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hm : P.m = 1) (l lam : ℕ) :
    (K x₀ l : ℝ) * ((P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1) : ℕ) : ℝ) ≤ 3 * ((g x₀ l : ℝ) ^ 4 * lam) := by
  have n4 := K_le_g x₀ l
  have hq : K x₀ l * (2 * g x₀ l / K x₀ l) ≤ 2 * g x₀ l := Nat.mul_div_le _ _
  have h : K x₀ l * (P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1)) ≤ 3 * (g x₀ l ^ 4 * lam) := by
    rw [hm]
    calc K x₀ l * (1 * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1))
        = (g x₀ l * g x₀ l ^ 2 * lam) * (K x₀ l * (2 * g x₀ l / K x₀ l) + K x₀ l) := by ring
      _ ≤ (g x₀ l * g x₀ l ^ 2 * lam) * (3 * g x₀ l) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (g x₀ l ^ 4 * lam) := by ring
  exact_mod_cast h
end GeneralPieces.Rate
