-- Prove2me | solution 1 for GeneralPieces.Bits.kappa_sqrt_pred_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:31:40.128875+00:00
-- url     : https://prove2.me/submissions/4078e0e6-0a03-40da-9f8b-8aefb63f1df0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_p_pred_lt
import Theorems.Thm_ClauseBound_Part_Bits_p_pred_lt
import Theorems.Thm_ClauseBound_Part_p_pos
import Theorems.Thm_GeneralPieces_hOfSpec


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) (hB0 : 0 ≤ B) {lam : ℕ} (hl : 1 ≤ lam) :
    kappa * √((AppHalfPieces.hOf lam : ℝ) - 1) < lam + B * logb 2 (AppHalfPieces.hOf lam) + C := by
  have h2 := (hOfSpec lam).1
  have h1 := hB.1 (AppHalfPieces.hOf lam - 1) (by omega)
  have h3 : logb 2 (p (AppHalfPieces.hOf lam - 1)) < lam := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast ClauseBound.Part.p_pos _), Real.rpow_natCast]
    exact_mod_cast p_pred_lt hl
  have h7 : ((AppHalfPieces.hOf lam - 1 : ℕ) : ℝ) = (AppHalfPieces.hOf lam : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hh0 : (2 : ℝ) ≤ AppHalfPieces.hOf lam := by exact_mod_cast h2
  rw [h7] at h1
  have h8 : logb 2 ((AppHalfPieces.hOf lam : ℝ) - 1) ≤ logb 2 (AppHalfPieces.hOf lam) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have h9 := mul_le_mul_of_nonneg_left h8 hB0
  linarith
end GeneralPieces.Bits
