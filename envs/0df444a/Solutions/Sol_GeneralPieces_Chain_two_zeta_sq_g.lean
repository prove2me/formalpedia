-- Prove2me | solution 1 for GeneralPieces.Chain.two_zeta_sq_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:07.919354+00:00
-- url     : https://prove2.me/submissions/c9d6ba86-c10c-4332-b47b-0a96767a5978

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (x₀ l : ℕ) (hx : 9 ≤ x₀) : 2 * zeta l ^ 2 * (g x₀ l : ℝ) = 2 ^ (l + x₀ - 9) * K x₀ l := by
  have hg : (g x₀ l : ℝ) = 2 ^ (3 * l + x₀) * K x₀ l := by rw [g]; push_cast; rfl
  obtain ⟨t, rfl⟩ : ∃ t, x₀ = t + 9 := ⟨x₀ - 9, by omega⟩
  have e1 : l + (t + 9) - 9 = l + t := by omega
  have e2 : (2 : ℝ) ^ (3 * l + (t + 9)) = 2 ^ (l + t) * 2 ^ 9 * (2 ^ l) ^ 2 := by ring
  rw [hg, zeta, e1, e2, pow_add 2 l 5]
  field_simp
end GeneralPieces.Chain
