-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.abs_piece_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:43:28.140726+00:00
-- url     : https://prove2.me/submissions/c02f0aea-194e-485d-9ef9-e83c81f4d93b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_wt_le_col
import Theorems.Thm_GeneralPieces_ThmHalfPieces_Rcol_le_Delta
import Theorems.Thm_GeneralPieces_ThmHalfPieces_card_terms_col
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Sizes_abs_factor_a_le
import Theorems.Thm_GeneralPieces_Sizes_abs_factor_b_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) :
    |piece h mu s x y u v| ≤ Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) := by
  have hw : ∀ z, wt (mu z) ≤ 4 * h := fun z => by rw [IsMu.wt hmu]; omega
  unfold piece
  rw [hP.col h _ _ _ _ s hh (IsMu.wt hmu x) (IsMu.wt hmu y) (IsMu.wt hmu u) (IsMu.wt hmu v)]
  generalize hK : ((2 : ℚ) ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2)) = K
  have hK0 : 0 ≤ K := by rw [← hK]; positivity
  have h1 : ∀ i ∈ range (2 * h + 1), ∀ σ ∈ ptnsZ (2 * h - s - i),
      |(-1 : ℚ) ^ i * coef (mu u) (op (angle h i (aFam (mu x))) (s - h + i) (tpow σ)) * coef σ (op (bFam (mu v)) (h - s - i) (tpow (mu y)))| ≤ K := by
    intro i _ σ hσ
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, ← hK]
    exact mul_le_mul (abs_factor_a_le hh i (IsMu.wt hmu x) _ (hw u) (wt_le_col hs hσ)) (abs_factor_b_le hh (IsMu.wt hmu v) _ (wt_le_col hs hσ) (hw y))
      (abs_nonneg _) (by positivity)
  calc _ ≤ ∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (2 * h - s - i), K :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun σ hσ => h1 i hi σ hσ))
    _ = (Rcol h s : ℚ) * K := by
        simp_rw [sum_const, nsmul_eq_mul]
        rw [← sum_mul, ← Nat.cast_sum, card_terms_col]
    _ ≤ Delta h * K := mul_le_mul_of_nonneg_right (by exact_mod_cast Rcol_le_Delta hs) hK0
end GeneralPieces.ThmHalfPieces
