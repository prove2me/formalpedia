-- Prove2me | solution 1 for GeneralPieces.Bits.exists_kappa_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:34:13.251658+00:00
-- url     : https://prove2.me/submissions/d4704764-d275-4218-b83c-14d3967f6808

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_bounds_abs
import Theorems.Thm_GeneralPieces_Bits_kappa_sqrt_pred_lt
import Theorems.Thm_GeneralPieces_Bits_exists_hOf_le
import Theorems.Thm_GeneralPieces_Bits_kappa_sqrt_le_pred
import Theorems.Thm_ClauseBound_Part_Bits_kappa_pos
import Theorems.Thm_GeneralPieces_hOfSpec


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) : ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ lam : ℕ, 1 ≤ lam →
    kappa * √(AppHalfPieces.hOf lam : ℝ) ≤ lam + c₁ * logb 2 (2 * lam) ∧ logb 2 (AppHalfPieces.hOf lam) ≤ c₂ * logb 2 (2 * lam) := by
  have hκ := ClauseBound.Part.Bits.kappa_pos
  obtain ⟨c₀, h0⟩ := exists_hOf_le hB
  have hc0 : 1 ≤ c₀ := by
    have h1 := h0 1 le_rfl
    have h2 := (hOfSpec 1).1
    omega
  have hc0' : (1 : ℝ) ≤ c₀ := by exact_mod_cast hc0
  have ha : 0 ≤ logb 2 c₀ := Real.logb_nonneg (by norm_num) hc0'
  refine ⟨|B| * (logb 2 c₀ + 2) + |C| + kappa, logb 2 c₀ + 2, by positivity, by positivity, fun lam hl => ?_⟩
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hx : 0 ≤ logb 2 lam := Real.logb_nonneg (by norm_num) hl0
  have hℓ : logb 2 (2 * lam) = 1 + logb 2 lam := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  have h2 := (hOfSpec lam).1
  have h3 : logb 2 (AppHalfPieces.hOf lam) ≤ (logb 2 c₀ + 2) * logb 2 (2 * lam) := by
    have h4 : ((AppHalfPieces.hOf lam : ℕ) : ℝ) ≤ c₀ * (lam : ℝ) ^ 2 := by exact_mod_cast h0 lam hl
    have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h4
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow] at h5
    rw [hℓ]
    push_cast at h5
    nlinarith [mul_nonneg ha hx]
  refine ⟨?_, h3⟩
  have h6 := kappa_sqrt_pred_lt (bounds_abs hB) (abs_nonneg B) hl
  have h12 := kappa_sqrt_le_pred (h := AppHalfPieces.hOf lam) (by omega)
  have h13 : |B| * logb 2 (AppHalfPieces.hOf lam) ≤ |B| * ((logb 2 c₀ + 2) * logb 2 (2 * lam)) := mul_le_mul_of_nonneg_left h3 (abs_nonneg B)
  have h14 : (1 : ℝ) ≤ logb 2 (2 * lam) := by rw [hℓ]; linarith
  have h15 : (|C| + kappa) * 1 ≤ (|C| + kappa) * logb 2 (2 * lam) := mul_le_mul_of_nonneg_left h14 (by positivity)
  nlinarith [le_abs_self C]
end GeneralPieces.Bits
