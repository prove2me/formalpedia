-- Prove2me | solution 1 for GeneralPieces.Rate.brute_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:57:31.744707+00:00
-- url     : https://prove2.me/submissions/d7197d7a-4f1d-4f7b-b926-bd1893893885

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (ρ : ℝ) (x₀ lam : ℕ) : ((K x₀ 0 * (K x₀ 0 - 1) / 2 * lam : ℕ) : ℝ) ≤ e ρ x₀ 0 * (K x₀ 0 : ℝ) ^ 2 * lam := by
  have h1 : 2 * (K x₀ 0 * (K x₀ 0 - 1) / 2 * lam) ≤ K x₀ 0 ^ 2 * lam := by
    calc 2 * (K x₀ 0 * (K x₀ 0 - 1) / 2 * lam) = 2 * (K x₀ 0 * (K x₀ 0 - 1) / 2) * lam := by ring
      _ ≤ K x₀ 0 * (K x₀ 0 - 1) * lam := Nat.mul_le_mul_right _ (Nat.mul_div_le _ _)
      _ ≤ K x₀ 0 * K x₀ 0 * lam := by gcongr; exact Nat.sub_le _ _
      _ = K x₀ 0 ^ 2 * lam := by ring
  have h2 : 2 * ((K x₀ 0 * (K x₀ 0 - 1) / 2 * lam : ℕ) : ℝ) ≤ (K x₀ 0 : ℝ) ^ 2 * lam := by exact_mod_cast h1
  rw [show e ρ x₀ 0 = 1 / 2 from rfl]
  linarith
end GeneralPieces.Rate
