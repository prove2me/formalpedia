-- Prove2me | solution 1 for MasulloRH.finite_prime_tail_le_seven_over_three_halves_power
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:40:29.277068+00:00
-- url     : https://prove2.me/submissions/6d2ea3a5-5359-4bca-af89-eb182f8a0a27

import Theorems.Thm_MasulloRH_dyadic_prime_tail_telescoping_bound
import Mathlib
open ArithmeticFunction Finset
open MasulloRH

theorem solution (N K : ℕ) (hN : 196 ≤ N) :
    (∑ j ∈ Ioc N K,(vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤ 7/(N:ℝ)^(3/2:ℝ) := by
  let f (j : ℕ) := vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
  let B (k : ℕ) := 2^k*N
  let E (n : ℕ) := 7/(n:ℝ)^(3/2:ℝ)
  have hB (k : ℕ) : N ≤ B k := by
    change N ≤ 2^k*N
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hstep (k : ℕ) : B (k+1) = 2*(B k) := by simp [B,pow_succ]; ring
  have hbound (k : ℕ) : (∑ j ∈ Ioc N (B k), f j) ≤ E N-E (B k) := by
    induction k with
    | zero => simp [B]
    | succ k ih =>
      have hh := dyadic_prime_tail_telescoping_bound (B k) (hN.trans (hB k))
      rw [hstep]
      have he : E (2*B k) = 7/(2*(B k:ℝ))^(3/2:ℝ) := by simp [E]
      change (∑ j ∈ Ioc (B k) (2*B k),f j) ≤ E (B k) - _ at hh
      rw [←he] at hh
      rw [←Ioc_union_Ioc_eq_Ioc (hB k) (show B k ≤ 2*B k by omega),
        sum_union (Ioc_disjoint_Ioc_of_le (le_refl (B k)))]
      linarith only [ih,hh]
  have hK : K ≤ B K := K.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hpos (j : ℕ) (hj : N < j) : 0 ≤ f j := by
    have h1 : 1 ≤ (j:ℝ) := by exact_mod_cast (show 1 ≤ j by omega)
    exact sub_nonneg.mpr (div_le_div_of_nonneg_left vonMangoldt_nonneg
      (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)))
  have hsub : (∑ j ∈ Ioc N K,f j) ≤ ∑ j ∈ Ioc N (B K),f j :=
    sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc le_rfl hK) (fun j hj _ => hpos j (mem_Ioc.mp hj).1)
  exact hsub.trans ((hbound K).trans (sub_le_self _ (by dsimp [E]; positivity)))
