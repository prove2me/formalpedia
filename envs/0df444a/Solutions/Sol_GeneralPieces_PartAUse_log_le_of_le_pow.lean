-- Prove2me | solution 1 for GeneralPieces.PartAUse.log_le_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:57:18.298629+00:00
-- url     : https://prove2.me/submissions/a588efd0-2ca9-4eae-87fc-108738258c35

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
theorem _root_.solution {l d : ℕ} {M : ℝ} (hM : 0 < M) (h : M ≤ (K x₀ l : ℝ) ^ d) : Real.logb 2 M ≤ d * Real.logb 2 (K x₀ l) := by
  have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hM h
  rwa [Real.logb_pow] at this
end GeneralPieces.PartAUse
