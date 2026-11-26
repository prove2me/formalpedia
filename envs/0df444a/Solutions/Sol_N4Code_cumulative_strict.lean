-- Prove2me | solution 1 for N4Code.cumulative_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:30.981867+00:00
-- url     : https://prove2.me/submissions/9638359e-72f7-49e1-9ae0-08731a302b02

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_lambda_diff_one_column
import Theorems.Thm_N4Code_abel_sum
import Theorems.Thm_N4Code_Psi_real
import Theorems.Thm_N4Code_r_pos
import Theorems.Thm_N4Code_r_lt_one
import Theorems.Thm_N4Code_r_pow_sub_pos

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0)
    (hgt : ∃ d ∈ Finset.Icc 1 n, Psi C t d > 0) :
    UniversalStrictBetter C' C := by
  intro ε hε0 hε1
  apply sub_pos.mp
  rw [lambda_diff_one_column C C' t hcol hcol' hsame ε hε0 hε1]
  have hSum : (0 : ℝ) < ∑ d ∈ Finset.Icc 1 n,
      ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1) := by
    rw [abel_sum (fun i => (alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ)) (ε / (1 - ε))]
    by_cases hn : n = 0
    · subst n
      exfalso
      rcases hgt with ⟨d, hd, _⟩
      simp at hd
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hC_nonneg : ∀ d ∈ Finset.Icc 1 (n - 1),
          0 ≤ (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd2 : d ≤ n - 1 := (Finset.mem_Icc.mp hd).2
        have hdn : d ≤ n := by omega
        rw [Psi_real C t d hd1]
        have hPd : 0 ≤ (Psi C t d : ℝ) := by
          exact_mod_cast hge d (by simp [Finset.mem_Icc, hd1, hdn])
        exact mul_nonneg hPd (le_of_lt (r_pow_sub_pos hε0 hε1 hd1))
      have hterm1 : 0 ≤ (∑ i ∈ Finset.Icc 1 n,
          ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) := by
        rw [Psi_real C t n hn1]
        have hPn : 0 ≤ (Psi C t n : ℝ) := by
          exact_mod_cast hge n (by simp [Finset.mem_Icc, hn1])
        exact mul_nonneg hPn (pow_nonneg (le_of_lt (r_pos hε0 hε1)) (n - 1))
      have hterm2 : 0 ≤ ∑ d ∈ Finset.Icc 1 (n - 1),
          (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
        exact Finset.sum_nonneg hC_nonneg
      rcases hgt with ⟨d0, hd0mem, hd0gt⟩
      have hd01 : 1 ≤ d0 := (Finset.mem_Icc.mp hd0mem).1
      have hd0n : d0 ≤ n := (Finset.mem_Icc.mp hd0mem).2
      by_cases hd0eq : d0 = n
      · have hterm1' : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) := by
          rw [Psi_real C t n hn1]
          have hPn : 0 < (Psi C t n : ℝ) := by
            have hgtn : Psi C t n > 0 := by
              simpa [hd0eq] using hd0gt
            exact_mod_cast hgtn
          exact mul_pos hPn (pow_pos (r_pos hε0 hε1) (n - 1))
        have hsum0 : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) +
            ∑ d ∈ Finset.Icc 1 (n - 1),
              (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
                ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          linarith
        exact hsum0
      · have hd0lt : d0 ≤ n - 1 := by omega
        have hd0mem' : d0 ∈ Finset.Icc 1 (n - 1) := by
          simp [Finset.mem_Icc, hd01, hd0lt]
        have hC : 0 < (∑ i ∈ Finset.Icc 1 d0,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
              ((ε / (1 - ε)) ^ (d0 - 1) - (ε / (1 - ε)) ^ d0) := by
          rw [Psi_real C t d0 hd01]
          have hP : 0 < (Psi C t d0 : ℝ) := by
            exact_mod_cast hd0gt
          exact mul_pos hP (r_pow_sub_pos hε0 hε1 hd01)
        have hB : (∑ i ∈ Finset.Icc 1 d0,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
              ((ε / (1 - ε)) ^ (d0 - 1) - (ε / (1 - ε)) ^ d0) ≤
            ∑ d ∈ Finset.Icc 1 (n - 1),
              (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
                ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          exact Finset.single_le_sum hC_nonneg hd0mem'
        have hsum0 : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) +
            ∑ d ∈ Finset.Icc 1 (n - 1),
              (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
                ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          linarith
        exact hsum0
  have hK : 0 < (1 - ε) ^ n / 4 * (1 - ε / (1 - ε)) := by
    have h1ε : 0 < 1 - ε := by linarith
    have hr1 : ε / (1 - ε) < 1 := r_lt_one hε1
    exact mul_pos (div_pos (pow_pos h1ε n) (by norm_num)) (by linarith)
  exact mul_pos hK hSum
end N4Code
