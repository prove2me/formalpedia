-- Prove2me | solution 1 for GeneralPieces.Rate.half_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:43.903505+00:00
-- url     : https://prove2.me/submissions/acd4c155-98d1-4b23-bd7a-40ed9462c74c

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
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_pow_le_K
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ) :
    (c + 5) * K x₀ l ^ 2 ≤ 2 ^ x₀ * K x₀ l ^ 2 ∧ 2 * (2 ^ x₀ * K x₀ l ^ 2) ≤ g x₀ l ^ 4 := by
  refine ⟨Nat.mul_le_mul_right _ hc, ?_⟩
  have h2 := pow_le_K hx l
  have h3 := big_le_K hx l
  have h4 := K_le_g x₀ l
  calc 2 * (2 ^ x₀ * K x₀ l ^ 2) = 2 * 2 ^ x₀ * K x₀ l ^ 2 := by ring
    _ ≤ g x₀ l * g x₀ l * g x₀ l ^ 2 := by
        gcongr
        · omega
        · omega
    _ = g x₀ l ^ 4 := by ring
end GeneralPieces.Rate
