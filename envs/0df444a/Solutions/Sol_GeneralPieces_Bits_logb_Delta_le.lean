-- Prove2me | solution 1 for GeneralPieces.Bits.logb_Delta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:32:20.256387+00:00
-- url     : https://prove2.me/submissions/789229be-e7ca-459e-bee0-a78a52fce66f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_logb_le_of_le_mul_p
import Theorems.Thm_ClauseBound_Part_p_pos
import Theorems.Thm_GeneralPieces_Sizes_Delta_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) (h : ℕ) : logb 2 (Delta h) ≤ 2 * (kappa * √(h : ℝ)) + logb 2 (4 * (h : ℝ) + 1) + C := by
  have h4 : 1 ≤ Delta h :=
    (ClauseBound.Part.p_pos 0).trans (single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))
  have h5 := logb_le_of_le_mul_p hB h4 (Nat.succ_pos _) (Delta_le h)
  have h6 : √((4 * h : ℕ) : ℝ) = 2 * √(h : ℝ) := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [h6] at h5
  push_cast at h5
  linarith
end GeneralPieces.Bits
