-- Prove2me | solution 1 for GeneralPieces.PartAUse.lt_pow_ninety
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:45:55.161582+00:00
-- url     : https://prove2.me/submissions/9416bab8-8d6f-435a-b62d-afea1f1bbdd6

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
theorem _root_.solution (hA : TheoremAa ρ x₀) {l m : ℕ} (h : m < K x₀ (l + 1) ^ 9) : m < K x₀ l ^ 90 :=
  calc m < K x₀ (l + 1) ^ 9 := h
    _ ≤ (K x₀ l ^ 10) ^ 9 := Nat.pow_le_pow_left (hA.K_lt_le l).2 9
    _ = K x₀ l ^ 90 := by rw [← pow_mul]
end GeneralPieces.PartAUse
