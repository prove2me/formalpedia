-- Prove2me | solution 1 for GilesMLMC.Complexity.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:42:49.844184+00:00
-- url     : https://prove2.me/submissions/e477c41d-6364-4801-ad9a-8e4103486f25

import Definitions.Def_GilesMLMC_Complexity_Setup
open GilesMLMC.Complexity

private lemma geometric_bound (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (n : ℕ) :
    ∑ l ∈ Finset.range n, q ^ l < (1 - q)⁻¹ := by
  have hid : (∑ l ∈ Finset.range n, q ^ l) * (1 - q) = 1 - q ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hp := pow_pos hq n
  rw [← one_div]
  apply (lt_div_iff₀ (by linarith : 0 < 1 - q)).2
  nlinarith

theorem solution
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β : ℝ) (hβ : 1 < β) (L : ℕ) :
    ∑ l ∈ Finset.range (L + 1), h M T l ^ ((β - 1) / 2) <
      T ^ ((β - 1) / 2) * (1 - (M : ℝ) ^ (-(β - 1) / 2))⁻¹ := by
  have hm : 1 < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hm0 : 0 < (M : ℝ) := by linarith
  let a := (β - 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have he (l : ℕ) : h M T l ^ a = T ^ a * ((M : ℝ) ^ (-a)) ^ l := by
    rw [h, Real.div_rpow hT.le (pow_nonneg hm0.le _), Real.rpow_pow_comm hm0.le,
      Real.rpow_neg (pow_nonneg hm0.le l), div_eq_mul_inv]
  have hq : 0 < (M : ℝ) ^ (-a) := Real.rpow_pos_of_pos hm0 _
  have hq1 : (M : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hm (by linarith)
  have hneg : -(β - 1) / 2 = -a := by dsimp [a]; ring
  rw [hneg]
  change ∑ l ∈ Finset.range (L + 1), h M T l ^ a <
    T ^ a * (1 - (M : ℝ) ^ (-a))⁻¹
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_lt_mul_of_pos_left (geometric_bound _ hq hq1 (L + 1))
    (Real.rpow_pos_of_pos hT a)

#print axioms solution
