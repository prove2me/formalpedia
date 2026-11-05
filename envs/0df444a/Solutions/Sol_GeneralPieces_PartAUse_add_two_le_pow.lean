-- Prove2me | solution 1 for GeneralPieces.PartAUse.add_two_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:52:09.018222+00:00
-- url     : https://prove2.me/submissions/a96af05b-f9b8-474f-80f6-454ade786e3a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_GeneralPieces_PartAUse_two_le_K
import Theorems.Thm_GeneralPieces_PartAUse_lt_pow_ninety
import Theorems.Thm_ClauseBound_Alg_TopArith_root9_spec
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}
namespace GeneralPieces.PartAUse
theorem _root_.solution (hA : TheoremAa ρ x₀) {l m : ℕ} (h : (root9 m).length < K x₀ (l + 1)) : m + 2 ≤ K x₀ l ^ 91 := by
  have h1 : m < K x₀ l ^ 90 := lt_pow_ninety hA (lt_of_lt_of_le (root9_spec m).2 (Nat.pow_le_pow_left (Nat.succ_le_of_lt h) 9))
  have h2 : K x₀ l ^ 91 = K x₀ l ^ 90 * K x₀ l := pow_succ _ _
  have h3 : K x₀ l ^ 90 * 2 ≤ K x₀ l ^ 90 * K x₀ l := Nat.mul_le_mul_left _ (two_le_K hA l)
  omega
end GeneralPieces.PartAUse
