-- Prove2me | solution 1 for GeneralPieces.Chain.total_eq_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:47:03.652235+00:00
-- url     : https://prove2.me/submissions/7daa9107-4a08-4aac-9a91-67fc86dda795

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
theorem _root_.solution (P : PiecesF) (a h lam y : ℕ) :
    totalG P a a (decide (totalG P a a true h lam y < totalG P a a false h lam y)) h lam y =
      min (totalG P a a false h lam y) (totalG P a a true h lam y) := by
  by_cases hlt : totalG P a a true h lam y < totalG P a a false h lam y
  · rw [decide_eq_true hlt, min_eq_right hlt.le]
  · rw [decide_eq_false hlt, min_eq_left (not_lt.1 hlt)]
end GeneralPieces.Chain
