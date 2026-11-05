-- Prove2me | solution 1 for GeneralPieces.Bits.logb_le_of_le_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:28:04.518612+00:00
-- url     : https://prove2.me/submissions/285da7f1-145b-4b74-982b-e2d0c6765efe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_ClauseBound_Part_p_pos


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) {r k a : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (h : r ≤ k * p a) :
    logb 2 r ≤ logb 2 k + kappa * √(a : ℝ) + C := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < p a := by exact_mod_cast ClauseBound.Part.p_pos a
  have h1 : (r : ℝ) ≤ k * p a := by exact_mod_cast h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hr0 h1
  rw [Real.logb_mul hk0.ne' hp0.ne'] at h2
  linarith [hB.2 a]
end GeneralPieces.Bits
