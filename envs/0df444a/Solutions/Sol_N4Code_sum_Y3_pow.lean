-- Prove2me | solution 1 for N4Code.sum_Y3_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:13.610029+00:00
-- url     : https://prove2.me/submissions/4c621163-1661-43ae-b834-fc77244aeef5

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_alpha3_zero
import Theorems.Thm_N4Code_sum_by_dist
import Theorems.Thm_N4Code_sum_Icc0_eq_Icc1

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (r : ℝ) :
    (∑ y ∈ Finset.univ.filter (Y3 C t), r ^ (dCode C y - 1)) =
      ∑ d ∈ Finset.Icc 1 n, (alpha3 C t d : ℝ) * r ^ (d - 1) := by
  have h0 : (alpha3 C t 0 : ℝ) = 0 := by simp [alpha3_zero C C' t hcol hcol' hsame]
  calc
    (∑ y ∈ Finset.univ.filter (Y3 C t), r ^ (dCode C y - 1))
        = ∑ d ∈ Finset.Icc 0 n, (alpha3 C t d : ℝ) * r ^ (d - 1) := by
          rw [sum_by_dist C (Y3 C t) (fun d => r ^ (d - 1))]
          simp [alpha3]
    _ = ∑ d ∈ Finset.Icc 1 n, (alpha3 C t d : ℝ) * r ^ (d - 1) := by
          exact sum_Icc0_eq_Icc1 (fun d => (alpha3 C t d : ℝ) * r ^ (d - 1))
            (by simp [h0])
end N4Code
