-- Prove2me | solution 1 for GilesMLMC.Complexity.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:44:20.387988+00:00
-- url     : https://prove2.me/submissions/dfee0d35-f3fb-4c47-998c-2552c7e55702

import Definitions.Def_GilesMLMC_Complexity_Setup
open GilesMLMC.Complexity

theorem solution
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β : ℝ) (hβ : β < 1) (L : ℕ) :
    ∑ l ∈ Finset.range (L + 1), h M T l ^ (-(1 - β) / 2) <
      h M T L ^ (-(1 - β) / 2) * (1 - (M : ℝ) ^ (-(1 - β) / 2))⁻¹ := by
  have hm : 1 < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hm0 : 0 < (M : ℝ) := by linarith
  let a := -(1 - β) / 2
  let q := (M : ℝ) ^ a
  have ha : a < 0 := by dsimp [a]; linarith
  have hq : 0 < q := Real.rpow_pos_of_pos hm0 _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hm ha
  have hd : 0 < 1 - q := by linarith
  have hp (l : ℕ) : 0 < h M T l ^ a :=
    Real.rpow_pos_of_pos (div_pos hT (pow_pos hm0 l)) _
  have he (l : ℕ) : h M T l ^ a = h M T (l + 1) ^ a * q := by
    have hs : h M T l = h M T (l + 1) * (M : ℝ) := by
      dsimp [h]; rw [pow_succ]; field_simp
    rw [hs, Real.mul_rpow (show 0 ≤ h M T (l + 1) from (div_pos hT (pow_pos hm0 _)).le) hm0.le]
  change ∑ l ∈ Finset.range (L + 1), h M T l ^ a < h M T L ^ a * (1 - q)⁻¹
  apply (lt_mul_inv_iff₀ hd).2
  induction L with
  | zero => simp only [Nat.zero_add, Finset.sum_range_one]; nlinarith [hp 0]
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hh := he L
    nlinarith

#print axioms solution
