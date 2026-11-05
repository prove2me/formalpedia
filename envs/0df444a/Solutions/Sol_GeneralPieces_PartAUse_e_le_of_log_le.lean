-- Prove2me | solution 1 for GeneralPieces.PartAUse.e_le_of_log_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:46:07.3837+00:00
-- url     : https://prove2.me/submissions/04745d45-5c1b-4938-98e2-02085c0e8361

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
theorem _root_.solution (hA : TheoremAa ρ x₀) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} {y d : ℝ} (hy : 0 < y) (hd : 0 ≤ d)
    (h : y ≤ d * Real.logb 2 (K x₀ l)) : e ρ x₀ l ≤ 0.85 * (d * (3 * x₀ + 6) / y) ^ Real.logb 2 (1 / ρ) := by
  have hα : 0 ≤ Real.logb 2 (1 / ρ) := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hρ]; linarith)
  have hlK : 0 < Real.logb 2 (K x₀ l) := by
    by_contra hc
    have := mul_nonneg hd (neg_nonneg.2 (not_lt.1 hc))
    linarith
  have h3 : (3 * (x₀ : ℝ) + 6) / Real.logb 2 (K x₀ l) ≤ d * (3 * x₀ + 6) / y := by
    rw [div_le_div_iff₀ hlK hy]
    have : (0 : ℝ) ≤ 3 * x₀ + 6 := by positivity
    nlinarith
  have h4 := Real.rpow_le_rpow (div_nonneg (by positivity) hlK.le) h3 hα
  linarith [(hA.e_bounds l).2, hA.rho_pow l]
end GeneralPieces.PartAUse
