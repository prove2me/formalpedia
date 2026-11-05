-- Prove2me | solution 1 for GeneralPieces.Rate.c_lam_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:43.5314+00:00
-- url     : https://prove2.me/submissions/54be4074-fabe-4693-89dc-35981a97ae85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_c_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l lam : ℕ) : K x₀ l * (c * lam) ≤ g x₀ l ^ 4 * lam := by
  have h1 := c_le_K hx hc l
  have h2 := K_le_g x₀ l
  have h3 : 1 ≤ g x₀ l := le_trans (by have := big_le_K hx l; omega) h2
  calc K x₀ l * (c * lam) = K x₀ l * c * 1 * lam := by ring
    _ ≤ g x₀ l * g x₀ l * g x₀ l ^ 2 * lam := by
        gcongr
        · exact h1.trans h2
        · exact Nat.one_le_pow _ _ h3
    _ = g x₀ l ^ 4 * lam := by ring
end GeneralPieces.Rate
