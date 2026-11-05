-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.abs_fa_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:38:04.388394+00:00
-- url     : https://prove2.me/submissions/348ae2c0-06bd-49ec-bcec-547925f9d691

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_cast_num_coef
import Theorems.Thm_GeneralPieces_ThmHalfPieces_three_le_eL
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Sizes_abs_factor_a_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (hP : PieceFacts) {h : ℕ} (hh : 1 ≤ h) (i : ℕ) {ξ : Ptn} (hξ : wt ξ = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |fa h i r ξ σ' σ| ≤ 2 ^ ClauseBound.Boson.Half.eL h := by
  have a1 := abs_factor_a_le hh i hξ r h1 h2
  rw [← cast_num_coef (hP.int_a h i ξ σ r) σ', ← pow_add] at a1
  have a2 : |(coef σ' (op (angle h i (aFam ξ)) r (tpow σ))).num| ≤ 2 ^ (3 * h + 12 * h ^ 2) := by exact_mod_cast a1
  rw [fa, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact a2.trans (pow_le_pow_right₀ (by norm_num) (three_le_eL h))
end GeneralPieces.ThmHalfPieces
