-- Prove2me | solution 1 for N4Code.sum_Y5_weight_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:14.216735+00:00
-- url     : https://prove2.me/submissions/eb5fd891-5e66-4688-ae93-22d1009c621b

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_y_rel_5
import Theorems.Thm_N4Code_weight_succ_diff
import Theorems.Thm_N4Code_dCode_le


set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (∑ y ∈ Finset.univ.filter (Y5 C t),
        (weight n ε (dCode C y + 1) - weight n ε (dCode C y))) =
      -((1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (Y5 C t), (ε / (1 - ε)) ^ (dCode C y)) := by
  calc
    (∑ y ∈ Finset.univ.filter (Y5 C t),
        (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))
        = ∑ y ∈ Finset.univ.filter (Y5 C t),
            -((1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (dCode C y)) := by
          apply Finset.sum_congr rfl
          intro y hy
          have h5 : Y5 C t y := (Finset.mem_filter.mp hy).2
          have hdn : dCode C y < n := by
            have h := (y_rel_5 C C' t hcol hcol' hsame h5).1
            have hle := dCode_le C' (flipBit t y)
            omega
          exact weight_succ_diff (n := n) (ε := ε) hε0 hε1 (d := dCode C y) hdn
    _ = -((1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (Y5 C t), (ε / (1 - ε)) ^ (dCode C y)) := by
          rw [Finset.sum_neg_distrib]
          rw [Finset.mul_sum]
end N4Code
