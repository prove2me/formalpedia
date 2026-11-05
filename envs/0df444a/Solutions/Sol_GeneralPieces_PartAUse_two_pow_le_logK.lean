-- Prove2me | solution 1 for GeneralPieces.PartAUse.two_pow_le_logK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:01:53.700216+00:00
-- url     : https://prove2.me/submissions/ccf8460f-6bc7-4adf-9c49-deaee11ebbde

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
theorem _root_.solution (hA : TheoremAa ρ x₀) (hx : 2 ≤ x₀) (l : ℕ) : (2 : ℝ) ^ (l + 1) ≤ Real.logb 2 (K x₀ l) := by
  have h1 : ((l + 1 : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := Nat.cast_le.2 Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx
  have h3 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  push_cast at h1
  have h4 : 0 ≤ (3 * (x₀ : ℝ) - 2) * ((2 : ℝ) ^ l - 1) := mul_nonneg (by linarith) (by linarith)
  rw [hA.logK, pow_succ]
  nlinarith
end GeneralPieces.PartAUse
