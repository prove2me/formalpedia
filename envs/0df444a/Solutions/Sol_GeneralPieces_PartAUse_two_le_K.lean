-- Prove2me | solution 1 for GeneralPieces.PartAUse.two_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:53:05.88469+00:00
-- url     : https://prove2.me/submissions/8af091e6-816a-4b2e-8303-950637a38af2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) (l : ℕ) : 2 ≤ K x₀ l := by
  have h := lt_of_lt_of_le (hA.K_lt_le l).1 (hA.K_lt_le l).2
  by_contra hc
  have h3 : K x₀ l = 0 ∨ K x₀ l = 1 := by omega
  rcases h3 with h3 | h3 <;> rw [h3] at h <;> norm_num at h
end GeneralPieces.PartAUse
