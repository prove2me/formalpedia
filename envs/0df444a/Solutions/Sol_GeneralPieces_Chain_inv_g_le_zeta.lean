-- Prove2me | solution 1 for GeneralPieces.Chain.inv_g_le_zeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:03:27.455332+00:00
-- url     : https://prove2.me/submissions/a15a6762-6b23-435f-86ac-15c39159e977

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_GeneralPieces_Chain_zeta_mul_g
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_pow_le_g


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (x₀ l : ℕ) (hx : 18 ≤ x₀) : 1 / (g x₀ l : ℝ) ≤ zeta l := by
  have hg : (0 : ℝ) < g x₀ l := by
    have := pow_le_g hx l
    exact_mod_cast lt_of_lt_of_le (by positivity) this
  have hK : (1 : ℝ) ≤ K x₀ l := by
    have := big_le_K hx l
    exact_mod_cast (by omega : 1 ≤ K x₀ l)
  rw [div_le_iff₀ hg, zeta_mul_g x₀ l (by omega)]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hK
end GeneralPieces.Chain
