-- Prove2me | solution 1 for N4Code.sum_Y3_weight_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:11.925938+00:00
-- url     : https://prove2.me/submissions/ea28a668-203e-4670-8f0e-58ac104b2531

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_y_rel_3
import Theorems.Thm_N4Code_weight_pred_diff
import Theorems.Thm_N4Code_dCode_le


set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (∑ y ∈ Finset.univ.filter (Y3 C t),
        (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) =
      (1 - ε) ^ n * (1 - ε / (1 - ε)) *
        ∑ y ∈ Finset.univ.filter (Y3 C t), (ε / (1 - ε)) ^ (dCode C y - 1) := by
  calc
    (∑ y ∈ Finset.univ.filter (Y3 C t),
        (weight n ε (dCode C y - 1) - weight n ε (dCode C y)))
        = ∑ y ∈ Finset.univ.filter (Y3 C t),
            (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (dCode C y - 1) := by
          apply Finset.sum_congr rfl
          intro y hy
          have h3 : Y3 C t y := (Finset.mem_filter.mp hy).2
          have hd1 : 1 ≤ dCode C y := by
            have h := (y_rel_3 C C' t hcol hcol' hsame h3).2
            omega
          have hdn : dCode C y ≤ n := dCode_le C y
          exact weight_pred_diff (n := n) (ε := ε) hε0 hε1 (d := dCode C y) hd1 hdn
    _ = (1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (Y3 C t), (ε / (1 - ε)) ^ (dCode C y - 1) := by
          rw [Finset.mul_sum]
end N4Code
