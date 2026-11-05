-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.abs_fb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:37:01.107194+00:00
-- url     : https://prove2.me/submissions/43d569d5-a4e8-4f96-84ce-c1982d900687

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_cast_num_coef
import Theorems.Thm_GeneralPieces_ThmHalfPieces_sq_le_eR
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Sizes_abs_factor_b_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (hP : PieceFacts) {h : ℕ} (hh : 1 ≤ h) {ν : Ptn} (hν : wt ν = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |fb r ν σ' σ| ≤ 2 ^ ClauseBound.Boson.Half.eR h := by
  have a1 := abs_factor_b_le hh hν r h1 h2
  rw [← cast_num_coef (hP.int_b ν σ r) σ'] at a1
  have a2 : |(coef σ' (op (bFam ν) r (tpow σ))).num| ≤ (h.factorial : ℤ) * 2 ^ (12 * h ^ 2) := by exact_mod_cast a1
  have a3 : h.factorial ≤ 2 ^ (h * h) := (Nat.factorial_le_pow h).trans (by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le h)
  have a4 : (h.factorial : ℤ) ≤ 2 ^ (h * h) := by exact_mod_cast a3
  calc |fb r ν σ' σ| ≤ (h.factorial : ℤ) * 2 ^ (12 * h ^ 2) := a2
    _ ≤ 2 ^ (h * h) * 2 ^ (12 * h ^ 2) := mul_le_mul_of_nonneg_right a4 (by positivity)
    _ = 2 ^ (h * h + 12 * h ^ 2) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (sq_le_eR h)
end GeneralPieces.ThmHalfPieces
