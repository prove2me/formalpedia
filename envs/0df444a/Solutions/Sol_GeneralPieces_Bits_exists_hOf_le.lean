-- Prove2me | solution 1 for GeneralPieces.Bits.exists_hOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:32:54.124264+00:00
-- url     : https://prove2.me/submissions/29586b66-79dd-45b6-bb01-a743aca4507b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_bounds_abs
import Theorems.Thm_GeneralPieces_Bits_kappa_sqrt_pred_lt
import Theorems.Thm_ClauseBound_Part_Bits_kappa_pos
import Theorems.Thm_ClauseBound_Part_Bits_logb_le_sqrt_sqrt
import Theorems.Thm_GeneralPieces_hOfSpec


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) : ∃ c₀ : ℕ, ∀ lam : ℕ, 1 ≤ lam → AppHalfPieces.hOf lam ≤ c₀ * lam ^ 2 := by
  have hκ := ClauseBound.Part.Bits.kappa_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 4 * |B| / Real.log 2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = D ^ 2 / (2 * kappa) + |B| + |C| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * (1 + G) / kappa := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨⌈M ^ 2⌉₊ + 1, fun lam hl => ?_⟩
  have h2 := (hOfSpec lam).1
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = AppHalfPieces.hOf lam - 1 := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by omega
  have hE0 : (1 : ℝ) ≤ E := by exact_mod_cast hE1
  have h14 : ((AppHalfPieces.hOf lam : ℕ) : ℝ) = E + 1 := by
    rw [hE, Nat.cast_sub (by omega)]
    push_cast
    ring
  have h1 := kappa_sqrt_pred_lt (bounds_abs hB) (abs_nonneg B) hl
  rw [h14, add_sub_cancel_right] at h1
  have h0 : logb 2 ((E : ℝ) + 1) ≤ 1 + logb 2 E := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) (show (E : ℝ) + 1 ≤ 2 * E by linarith)
    rwa [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at this
  have h0' := mul_le_mul_of_nonneg_left h0 (abs_nonneg B)
  have h3 := ClauseBound.Part.Bits.logb_le_sqrt_sqrt hE1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = √√(E : ℝ) := ⟨_, rfl⟩
  have hy2 : y ^ 2 = √(E : ℝ) := by rw [hy, Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [← hy] at h3
  have h4 : |B| * Real.logb 2 E ≤ D * y := by
    have := mul_le_mul_of_nonneg_left h3 (abs_nonneg B)
    rw [hD]
    calc |B| * Real.logb 2 E ≤ |B| * (4 * y / Real.log 2) := this
      _ = 4 * |B| / Real.log 2 * y := by ring
  have h5 : D * y ≤ kappa * y ^ 2 / 2 + D ^ 2 / (2 * kappa) := by
    have h6 : kappa * y ^ 2 / 2 + D ^ 2 / (2 * kappa) - D * y = (kappa * y - D) ^ 2 / (2 * kappa) := by
      field_simp
      ring
    have h7 : 0 ≤ (kappa * y - D) ^ 2 / (2 * kappa) := by positivity
    linarith
  have h8 : kappa * √(E : ℝ) < 2 * (lam + G) := by
    rw [← hy2] at h1 ⊢
    rw [hG]
    linarith [le_abs_self C]
  have h9 : √(E : ℝ) < M * lam := by
    have h10 : 2 * (lam + G) ≤ 2 * (1 + G) * lam := by nlinarith
    have h11 : M * lam = 2 * (1 + G) * lam / kappa := by rw [hM]; ring
    rw [h11, lt_div_iff₀ hκ, mul_comm]
    linarith
  have h12 : (E : ℝ) < M ^ 2 * lam ^ 2 := by
    have h13 : (√(E : ℝ)) ^ 2 < (M * lam) ^ 2 := pow_lt_pow_left₀ h9 (Real.sqrt_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt (Nat.cast_nonneg _), mul_pow] at h13
  have h15 : ((AppHalfPieces.hOf lam : ℕ) : ℝ) ≤ (((⌈M ^ 2⌉₊ + 1) * lam ^ 2 : ℕ) : ℝ) := by
    have h16 := Nat.le_ceil (M ^ 2)
    have h17 : (1 : ℝ) ≤ (lam : ℝ) ^ 2 := one_le_pow₀ hl0
    have h18 : M ^ 2 * (lam : ℝ) ^ 2 ≤ (⌈M ^ 2⌉₊ : ℝ) * (lam : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h16 (by positivity)
    push_cast
    rw [h14]
    linarith
  exact_mod_cast h15
end GeneralPieces.Bits
