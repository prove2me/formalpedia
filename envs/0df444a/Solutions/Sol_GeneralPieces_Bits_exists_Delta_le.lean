-- Prove2me | solution 1 for GeneralPieces.Bits.exists_Delta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:35:50.263413+00:00
-- url     : https://prove2.me/submissions/c23149f6-d6c9-4b91-8e72-3f09a5ab06a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_exists_kappa_sqrt_le
import Theorems.Thm_GeneralPieces_Bits_logb_Delta_le
import Theorems.Thm_GeneralPieces_Bits_logb_two_mul_le
import Theorems.Thm_ClauseBound_Part_Bits_le_two_pow_of_logb_le
import Theorems.Thm_ClauseBound_Part_Bits_logb_succ_le
import Theorems.Thm_ClauseBound_Part_p_pos
import Theorems.Thm_GeneralPieces_hOfSpec


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → Delta (AppHalfPieces.hOf lam) ≤ 2 ^ (c * lam) := by
  obtain ⟨c₁, c₂, hc1, hc2, hcore⟩ := exists_kappa_sqrt_le hB
  refine ⟨⌈5 + 2 * c₁ + c₂ + |C|⌉₊, fun lam hl => ?_⟩
  obtain ⟨h1, h2⟩ := hcore lam hl
  have hh := (hOfSpec lam).1
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hL := logb_two_mul_le hl
  have h3 := logb_Delta_le hB (AppHalfPieces.hOf lam)
  have h4 := ClauseBound.Part.Bits.logb_succ_le (k := 4) (h := AppHalfPieces.hOf lam) le_rfl (by omega)
  push_cast at h4
  have h5 : 1 ≤ Delta (AppHalfPieces.hOf lam) :=
    (ClauseBound.Part.p_pos 0).trans (single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))
  have h6 := Nat.le_ceil (5 + 2 * c₁ + c₂ + |C|)
  have h7 := mul_le_mul_of_nonneg_right h6 (zero_le_one.trans hl0)
  have h8 := mul_le_mul_of_nonneg_left hL hc1
  have h9 := mul_le_mul_of_nonneg_left hL hc2
  have h10 : (3 + |C|) * 1 ≤ (3 + |C|) * lam := mul_le_mul_of_nonneg_left hl0 (by positivity)
  refine ClauseBound.Part.Bits.le_two_pow_of_logb_le h5 h3 ?_
  push_cast
  nlinarith [le_abs_self C]
end GeneralPieces.Bits
