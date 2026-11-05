-- Prove2me | solution 1 for GeneralPieces.Chain.stChain2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:06.483002+00:00
-- url     : https://prove2.me/submissions/f1ac5dd5-7159-41cd-97c5-71b63981892a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_GeneralPieces_Chain_levelOK2
import Theorems.Thm_ClauseBound_Gen_Rate_K_succ
import Theorems.Thm_ClauseBound_Gen_Rate_step_K
import Theorems.Thm_ClauseBound_Gen_Rate_step_d
import Theorems.Thm_ClauseBound_Gen_Rate_step_p


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution : StChain2 := by
  intro P ρ c x₀ hP hm hx₀ _ l
  induction l with
  | zero => intro lam _; rfl
  | succ l ih =>
    intro lam hlam
    refine ⟨?_, levelOK2 hP hm x₀ hx₀ l lam hlam, ?_⟩
    · rw [step_p, step_d, K_succ, sq]
    · rw [step_K]
      exact ih _ (Nat.le_add_left 1 _)
end GeneralPieces.Chain
