-- Prove2me | solution 1 for GeneralPieces.thmHalfPiecesPure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:46:14.900175+00:00
-- url     : https://prove2.me/submissions/24b950ea-d4ac-4035-85d2-cb70a3575def

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_cast_A
import Theorems.Thm_GeneralPieces_ThmHalfPieces_sum_A
import Theorems.Thm_GeneralPieces_ThmHalfPieces_row_A
import Theorems.Thm_GeneralPieces_ThmHalfPieces_col_A
import Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_A_lt
import Theorems.Thm_ClauseBound_Boson_Final_big_le
import Theorems.Thm_ClauseBound_Boson_Final_factorial_lt_two_pow_big
import Theorems.Thm_ClauseBound_Boson_Final_factorsThrough_mono
import Theorems.Thm_ClauseBound_Boson_Final_four_mul_add_one_le_big
import Theorems.Thm_ClauseBound_Part_exists_bounds
import Theorems.Thm_GeneralPieces_Bits_exists_Delta_le
import Theorems.Thm_GeneralPieces_Bits_exists_bits_le
import Theorems.Thm_GeneralPieces_Bits_exists_hOf_le
import Theorems.Thm_GeneralPieces_Lex_existsUnique_isMu
import Theorems.Thm_GeneralPieces_hOfSpec


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces Finset GeneralPieces.ThmHalfPieces ClauseBound.Boson.Final
namespace GeneralPieces
theorem _root_.solution (hP : AppHalfPieces.PieceFacts) : AppHalfPieces.ThmHalfPiecesPure := by
  obtain ⟨B, C, hB⟩ := ClauseBound.Part.exists_bounds
  obtain ⟨c₁, hbits⟩ := Bits.exists_bits_le hB
  obtain ⟨c₀, hh0⟩ := Bits.exists_hOf_le hB
  obtain ⟨c₂, hall⟩ := Bits.exists_Delta_le hB
  refine ⟨c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂), fun lam hl => ?_⟩
  have hbig := big_le (c₁ := c₁) hl (hh0 lam hl) (hall lam hl)
  generalize hc : c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂) = c at hbig ⊢
  have hc1 : c₁ ≤ c := by omega
  have hbits := hbits lam hl
  have h2 := (hOfSpec lam).1
  have hp := (hOfSpec lam).2.1
  generalize AppHalfPieces.hOf lam = h at *
  have hh : 1 ≤ h := by omega
  obtain ⟨mu, hmu, -⟩ := Lex.existsUnique_isMu hp
  have hpow : (2 : ℤ) ^ ClauseBound.Boson.big h ≤ 2 ^ (2 * lam) ^ c := pow_le_pow_right₀ (by norm_num) hbig
  have hI : ∀ i ∈ (fam h mu).I, |i| ≤ 2 * (h : ℤ) := fun i hi => by
    obtain ⟨a, b⟩ := mem_Icc.1 hi
    exact abs_le.2 ⟨a, b⟩
  refine ⟨mu, fam h mu, hmu, ?_, rfl, rfl, cast_A hP hmu hh, fun _ => rfl, fun _ => rfl⟩
  exact
    { d_pos := by
        change (1 : ℤ) ≤ (h.factorial : ℤ)
        exact_mod_cast h.factorial_pos
      sum_eq := sum_A hP hmu hh
      row := fun i hi => factorsThrough_mono (row_A hP hmu hh (hI i hi)) hpow
      col := fun i hi => factorsThrough_mono (col_A hP hmu hh (hI i hi)) hpow
      caps := fun i hi => by
        have hL : 0 ≤ Real.logb 2 (2 * (lam : ℝ)) := Real.logb_nonneg one_lt_two (by
          have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
          linarith)
        have hcc : (c₁ : ℝ) * Real.logb 2 (2 * (lam : ℝ)) ≤ (c : ℝ) * Real.logb 2 (2 * (lam : ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc1) hL
        exact (hbits i (hI i hi)).trans (by linarith)
      card_I := by
        change #(Icc (-(2 * h : ℤ)) (2 * h)) ≤ _
        rw [Int.card_Icc]
        have := four_mul_add_one_le_big h
        omega
      abs_d := by
        change (h.factorial : ℤ) < _
        exact lt_of_lt_of_le (by exact_mod_cast factorial_lt_two_pow_big h) hpow
      abs_I := fun i hi => by
        have h1 : 2 * h < 2 ^ ClauseBound.Boson.big h :=
          (Nat.lt_two_pow_self (n := 2 * h)).trans_le (Nat.pow_le_pow_right (by norm_num) (by have := four_mul_add_one_le_big h; omega))
        have h3 : (2 * (h : ℤ)) < 2 ^ ClauseBound.Boson.big h := by exact_mod_cast h1
        exact ((hI i hi).trans_lt h3).trans_le hpow
      abs_A := fun i hi x y u v => (abs_A_lt hP hmu hh (hI i hi) x y u v).trans_le hpow }
end GeneralPieces
