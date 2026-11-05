-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_bFam_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:31:27.448146+00:00
-- url     : https://prove2.me/submissions/a8dc7b8b-9537-4374-98dd-f22c047b7072

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_nonneg
import Theorems.Thm_GeneralPieces_Sizes_l1_smul
import Theorems.Thm_GeneralPieces_Sizes_l1_monomial_le
import Theorems.Thm_GeneralPieces_Sizes_zz_pos
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (μ : Ptn) : l1 (bFam μ) ≤ (wt μ).factorial := by
  unfold bFam
  rw [l1_smul]
  have a1 : l1 (tpow μ) ≤ 1 := (l1_monomial_le _ _).trans_eq abs_one
  have a2 : (1 : ℚ) ≤ zz μ := by exact_mod_cast zz_pos μ
  have a3 : |((wt μ).factorial : ℚ) / zz μ| ≤ (wt μ).factorial := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self (Nat.cast_nonneg _) a2
  calc _ ≤ ((wt μ).factorial : ℚ) * 1 := mul_le_mul a3 a1 (l1_nonneg _) (Nat.cast_nonneg _)
    _ = _ := mul_one _
end GeneralPieces.Sizes
