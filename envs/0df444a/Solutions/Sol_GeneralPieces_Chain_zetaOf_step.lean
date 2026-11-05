-- Prove2me | solution 1 for GeneralPieces.Chain.zetaOf_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:57:09.587979+00:00
-- url     : https://prove2.me/submissions/08a6f8fb-f62c-468d-aa3c-094174ad68d6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_ClauseBound_Gen_Rate_step_D__34894c


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (hm : P.m = 1) (x₀ l : ℕ) : zetaOf (step P x₀ l) = zeta l := by
  rw [zetaOf, step_D, hm, zeta, pow_succ 2 (l + 4)]
  push_cast
  field_simp
end GeneralPieces.Chain
