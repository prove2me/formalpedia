-- Prove2me | solution 1 for GeneralPieces.DefGenPieces.logb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:07:33.089968+00:00
-- url     : https://prove2.me/submissions/5eba8222-2859-4e37-bc15-e696c9791eab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Trim_Cert
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_Conv

set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open GeneralPieces.DefGenPieces
namespace GeneralPieces.DefGenPieces
theorem _root_.solution {lam : ℕ} (hl : 1 ≤ lam) : Real.logb 2 (2 * lam) ≤ lam := by
  have h0 : 2 * lam ≤ 2 ^ lam := by
    obtain ⟨k, rfl⟩ : ∃ k, lam = k + 1 := ⟨lam - 1, by omega⟩
    have := Nat.lt_two_pow_self (n := k)
    rw [pow_succ]
    omega
  have h1 : (0 : ℝ) < 2 * lam := by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    linarith
  have h2 : Real.logb 2 (2 * lam) ≤ Real.logb 2 ((2 : ℝ) ^ lam) := Real.logb_le_logb_of_le (by norm_num) h1 (by exact_mod_cast h0)
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
end GeneralPieces.DefGenPieces
