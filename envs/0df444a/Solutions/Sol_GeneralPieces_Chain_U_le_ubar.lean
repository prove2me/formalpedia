-- Prove2me | solution 1 for GeneralPieces.Chain.U_le_ubar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:45:54.134451+00:00
-- url     : https://prove2.me/submissions/6239fd12-e153-4035-ad57-cf614bf591d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_GeneralPieces_Chain_total_eq_min
import Theorems.Thm_GeneralPieces_Chain_ubar_eq
import Theorems.Thm_ClauseBound_Gen_Chain_total_min_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (hP : Par P ρ c) (x₀ l lam y : ℕ) (hlam : 1 ≤ lam) :
    min (totalG P (g x₀ l) (g x₀ l) false 0 lam y) (totalG P (g x₀ l) (g x₀ l) true 0 lam y) ≤ ubarG P (step P x₀ l) lam := by
  rw [← total_eq_min, ubar_eq]
  exact ClauseBound.Gen.Chain.total_min_le P (g x₀ l) 0 lam y (hP.spec 0 lam hlam).cnt_pos
end GeneralPieces.Chain
