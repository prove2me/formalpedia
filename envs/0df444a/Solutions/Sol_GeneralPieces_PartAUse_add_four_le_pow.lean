-- Prove2me | solution 1 for GeneralPieces.PartAUse.add_four_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:46:08.475537+00:00
-- url     : https://prove2.me/submissions/d3e50bb7-5114-4364-aadd-f996de59fe59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_GeneralPieces_PartAUse_two_le_K

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) {l n : ℕ} (hlt : n < K x₀ (l + 1) ^ 17) : n + 4 ≤ K x₀ l ^ 171 := by
  have h1 : K x₀ (l + 1) ^ 17 ≤ (K x₀ l ^ 10) ^ 17 := Nat.pow_le_pow_left (hA.K_lt_le l).2 17
  have h2 : (K x₀ l ^ 10) ^ 17 = K x₀ l ^ 170 := by rw [← pow_mul]
  have h3 : K x₀ l ^ 171 = K x₀ l ^ 170 * K x₀ l := pow_succ _ _
  have h4 : 2 ^ 170 ≤ K x₀ l ^ 170 := Nat.pow_le_pow_left (two_le_K hA l) 170
  have h5 : K x₀ l ^ 170 * 2 ≤ K x₀ l ^ 170 * K x₀ l := Nat.mul_le_mul_left _ (two_le_K hA l)
  have h6 : 4 ≤ 2 ^ 170 := by norm_num
  omega
end GeneralPieces.PartAUse
