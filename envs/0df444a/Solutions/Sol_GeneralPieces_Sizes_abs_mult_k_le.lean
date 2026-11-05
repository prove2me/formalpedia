-- Prove2me | solution 1 for GeneralPieces.Sizes.abs_mult_k_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:29:32.264532+00:00
-- url     : https://prove2.me/submissions/380a3bd2-602b-44e0-a0aa-02905575d81a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_le_wt
import Theorems.Thm_GeneralPieces_Sizes_mul_count_le_wt
import Theorems.Thm_GeneralPieces_Sizes_abs_binom_le
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} {n k : ℕ+} (hn : (n : ℕ) ≤ h) {σ : Ptn} (h2 : wt σ ≤ 4 * h) (hk : k ∈ σ) :
    |binom (-((k : ℕ) : ℤ) - 1) ((n : ℤ) - 1) * ((k : ℕ) * σ.count k)| ≤ 4 * h * 2 ^ (5 * h) := by
  have a1 := le_wt hk
  have a0 := n.pos
  have a2 : (2 : ℤ) ^ ((-((k : ℕ) : ℤ) - 1).natAbs + ((n : ℕ) - 1)) ≤ 2 ^ (5 * h) := pow_le_pow_right₀ (by norm_num) (by omega)
  have a3 : (((k : ℕ) : ℤ) * σ.count k) ≤ 4 * h := by exact_mod_cast (mul_count_le_wt σ k).trans h2
  have a4 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) * σ.count k := by positivity
  rw [abs_mul, abs_of_nonneg a4, mul_comm]
  exact mul_le_mul a3 ((abs_binom_le _ n).trans a2) (abs_nonneg _) (by positivity)
end GeneralPieces.Sizes
