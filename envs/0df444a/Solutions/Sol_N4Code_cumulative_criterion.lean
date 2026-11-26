-- Prove2me | solution 1 for N4Code.cumulative_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:10.91769+00:00
-- url     : https://prove2.me/submissions/ff65a96a-d164-4f69-9f27-391858e43ecb

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_lambda_diff_one_column
import Theorems.Thm_N4Code_abel_sum
import Theorems.Thm_N4Code_Psi_real

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hΨ : ∀ d ∈ Finset.Icc 1 n, Psi C t d = 0) : UniversalEqual C' C := by
  intro ε hε0 hε1
  apply sub_eq_zero.mp
  rw [lambda_diff_one_column C C' t hcol hcol' hsame ε hε0 hε1]
  have hSum : (∑ d ∈ Finset.Icc 1 n,
      ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1)) = 0 := by
    rw [abel_sum (fun i => (alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ)) (ε / (1 - ε))]
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hterm1 : (∑ i ∈ Finset.Icc 1 n,
          ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) = 0 := by
        rw [Psi_real C t n hn1, hΨ n (by simp [Finset.mem_Icc, hn1])]
        norm_num
      have hterm2 : (∑ d ∈ Finset.Icc 1 (n - 1),
          (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d)) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd2 : d ≤ n - 1 := (Finset.mem_Icc.mp hd).2
        have hdn : d ≤ n := by omega
        rw [Psi_real C t d hd1, hΨ d (by simp [Finset.mem_Icc, hd1, hdn])]
        norm_num
      rw [hterm1, hterm2]
      ring
  rw [hSum]
  ring
end N4Code
