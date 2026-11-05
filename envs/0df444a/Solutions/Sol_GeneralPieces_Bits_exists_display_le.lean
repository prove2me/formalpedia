-- Prove2me | solution 1 for GeneralPieces.Bits.exists_display_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:38:55.927949+00:00
-- url     : https://prove2.me/submissions/bcaf8786-6817-43fb-b067-c82a7897dd29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_exists_kappa_sqrt_le
import Theorems.Thm_ClauseBound_Part_Bits_logb_succ_le
import Theorems.Thm_GeneralPieces_hOfSpec


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam →
    2 * √2 * (kappa * √(AppHalfPieces.hOf lam : ℝ)) + 2 * logb 2 (2 * (AppHalfPieces.hOf lam : ℝ) + 1) + 2 * C + 2 ≤ 2 * √2 * lam + c * logb 2 (2 * lam) := by
  obtain ⟨c₁, c₂, hc1, hc2, hcore⟩ := exists_kappa_sqrt_le hB
  refine ⟨⌈8 + 2 * c₂ + 2 * |C| + 2 * √2 * c₁⌉₊, fun lam hl => ?_⟩
  obtain ⟨h1, h2⟩ := hcore lam hl
  have hh := (hOfSpec lam).1
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hℓ : (1 : ℝ) ≤ logb 2 (2 * lam) := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
    linarith [Real.logb_nonneg (b := 2) (by norm_num) hl0]
  have h6 := ClauseBound.Part.Bits.logb_succ_le (k := 2) (h := AppHalfPieces.hOf lam) (by norm_num) (by omega)
  have h8 : 2 * √2 * (kappa * √(AppHalfPieces.hOf lam : ℝ)) ≤ 2 * √2 * (lam + c₁ * logb 2 (2 * lam)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h9 := Nat.le_ceil (8 + 2 * c₂ + 2 * |C| + 2 * √2 * c₁)
  have h10 := mul_le_mul_of_nonneg_right h9 (zero_le_one.trans hℓ)
  have h11 : (8 + 2 * |C|) * 1 ≤ (8 + 2 * |C|) * logb 2 (2 * lam) := mul_le_mul_of_nonneg_left hℓ (by positivity)
  have h12 := le_abs_self C
  push_cast at h6
  nlinarith
end GeneralPieces.Bits
