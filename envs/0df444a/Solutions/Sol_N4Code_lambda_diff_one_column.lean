-- Prove2me | solution 1 for N4Code.lambda_diff_one_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:10.027+00:00
-- url     : https://prove2.me/submissions/b204b311-bca5-41aa-897b-7ec513194490

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_sum_Y3_pow
import Theorems.Thm_N4Code_sum_Y5_pow
import Theorems.Thm_N4Code_sum_Y3_weight_diff
import Theorems.Thm_N4Code_sum_Y5_weight_diff
import Theorems.Thm_N4Code_lambda_diff_y3y5

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      lambda C' ε - lambda C ε =
        ((1 - ε) ^ n / 4) * (1 - ε / (1 - ε)) *
          ∑ d ∈ Finset.Icc 1 n,
            ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) *
              (ε / (1 - ε)) ^ (d - 1) := by
  intro ε hε0 hε1
  rw [lambda_diff_y3y5 C C' t hcol hcol' hsame ε]
  rw [sum_Y3_weight_diff C C' t hcol hcol' hsame ε hε0 hε1,
      sum_Y5_weight_diff C C' t hcol hcol' hsame ε hε0 hε1]
  rw [sum_Y3_pow C C' t hcol hcol' hsame (ε / (1 - ε)),
      sum_Y5_pow C C' t hcol hcol' hsame (ε / (1 - ε))]
  have hsum :
      (∑ d ∈ Finset.Icc 1 n, (alpha3 C t d : ℝ) * (ε / (1 - ε)) ^ (d - 1)) -
        ∑ d ∈ Finset.Icc 1 n, (alpha5 C t (d - 1) : ℝ) * (ε / (1 - ε)) ^ (d - 1) =
      ∑ d ∈ Finset.Icc 1 n,
        ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [← hsum]
  ring
end N4Code
