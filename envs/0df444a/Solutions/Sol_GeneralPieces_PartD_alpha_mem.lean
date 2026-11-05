-- Prove2me | solution 1 for GeneralPieces.PartD.alpha_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:24:54.311599+00:00
-- url     : https://prove2.me/submissions/21bad9ad-85f3-4b29-be05-1e19c6f844f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_Main
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartD

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartD
namespace GeneralPieces.PartD
theorem _root_.solution (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) : 0 ≤ Real.logb 2 (1 / ρ) ∧ Real.logb 2 (1 / ρ) ≤ 1 := by
  have hρ0 : 0 < ρ := by linarith
  constructor
  · exact Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hρ0]; linarith)
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hρ0]
    linarith
end GeneralPieces.PartD
