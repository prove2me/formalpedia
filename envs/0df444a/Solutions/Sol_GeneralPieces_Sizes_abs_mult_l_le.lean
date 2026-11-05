-- Prove2me | solution 1 for GeneralPieces.Sizes.abs_mult_l_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:28:52.738576+00:00
-- url     : https://prove2.me/submissions/02301864-87ca-4b6b-b400-653583dcb710

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_le_wt
import Theorems.Thm_GeneralPieces_Sizes_abs_binom_le
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) {n l : ℕ+} (hn : (n : ℕ) ≤ h) {σ' : Ptn} (h1 : wt σ' ≤ 4 * h) (hl : l ∈ σ') :
    |binom (((l : ℕ) : ℤ) - 1) ((n : ℤ) - 1)| ≤ 4 * h * 2 ^ (5 * h) := by
  have a1 := le_wt hl
  have a2 : (2 : ℤ) ^ ((((l : ℕ) : ℤ) - 1).natAbs + ((n : ℕ) - 1)) ≤ 2 ^ (5 * h) := pow_le_pow_right₀ (by norm_num) (by omega)
  have a3 : (1 : ℤ) ≤ 4 * h := by omega
  calc _ ≤ (2 : ℤ) ^ (5 * h) := (abs_binom_le _ n).trans a2
    _ = 1 * 2 ^ (5 * h) := (one_mul _).symm
    _ ≤ 4 * h * 2 ^ (5 * h) := mul_le_mul_of_nonneg_right a3 (by positivity)
end GeneralPieces.Sizes
