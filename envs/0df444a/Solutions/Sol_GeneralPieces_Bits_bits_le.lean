-- Prove2me | solution 1 for GeneralPieces.Bits.bits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:32:48.304917+00:00
-- url     : https://prove2.me/submissions/51d50d62-6535-4d8d-b236-12e498e43ac5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_Rrow_le
import Theorems.Thm_GeneralPieces_Bits_Rcol_le
import Theorems.Thm_GeneralPieces_Bits_sqrt_add_sqrt_le
import Theorems.Thm_GeneralPieces_Bits_logb_le_of_le_mul_p
import Theorems.Thm_ClauseBound_Part_Bits_clog_le
import Theorems.Thm_ClauseBound_Part_Bits_kappa_pos
import Theorems.Thm_ClauseBound_Part_one_le_Rcol
import Theorems.Thm_ClauseBound_Part_one_le_Rrow


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    ((Nat.clog 2 (Rrow h s) + Nat.clog 2 (Rcol h s) : ℕ) : ℝ) ≤ 2 * √2 * (kappa * √(h : ℝ)) + 2 * logb 2 (2 * (h : ℝ) + 1) + 2 * C + 2 := by
  obtain ⟨a1, a2⟩ := abs_le.1 hs
  have r1 : 1 ≤ Rrow h s := ClauseBound.Part.one_le_Rrow hs
  have r2 : 1 ≤ Rcol h s := ClauseBound.Part.one_le_Rcol hs
  have q1 : pZ (2 * h + s) = p (2 * (h : ℤ) + s).toNat := if_pos (by omega)
  have q2 : pZ (2 * h - s) = p (2 * (h : ℤ) - s).toNat := if_pos (by omega)
  have c1 : (((2 * (h : ℤ) + s).toNat : ℕ) : ℝ) = 2 * (h : ℝ) + s := by
    have : (((2 * (h : ℤ) + s).toNat : ℕ) : ℤ) = 2 * (h : ℤ) + s := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have c2 : (((2 * (h : ℤ) - s).toNat : ℕ) : ℝ) = 2 * (h : ℝ) - s := by
    have : (((2 * (h : ℤ) - s).toNat : ℕ) : ℤ) = 2 * (h : ℤ) - s := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have h3 := ClauseBound.Part.Bits.clog_le r1 (logb_le_of_le_mul_p hB r1 (Nat.succ_pos _) (q1 ▸ Rrow_le h s))
  have h4 := ClauseBound.Part.Bits.clog_le r2 (logb_le_of_le_mul_p hB r2 (Nat.succ_pos _) (q2 ▸ Rcol_le h s))
  rw [c1] at h3
  rw [c2] at h4
  have h5 := mul_le_mul_of_nonneg_left (sqrt_add_sqrt_le hs) ClauseBound.Part.Bits.kappa_pos.le
  have h6 : √(2 * (h : ℝ)) = √2 * √(h : ℝ) := Real.sqrt_mul (by norm_num) _
  rw [h6] at h5
  push_cast at h3 h4 ⊢
  linarith
end GeneralPieces.Bits
