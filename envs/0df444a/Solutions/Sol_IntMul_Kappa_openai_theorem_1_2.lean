-- Prove2me | solution 2 for IntMul.Kappa.openai_theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T19:17:14.600175+00:00
-- url     : https://prove2.me/submissions/e83cd0c1-6604-4882-bb12-a1c8b669811b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_IntMul_Kappa_jain_round6

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul IntMul.Kappa

theorem solution : KappaBound (1 / 2 ^ 182) := by
  have hj : KappaBound (3666565558019 / 10 ^ 17) := jain_round6
  change MulTimeBound (fun n : ℕ =>
    (n : ℝ) * ((lg n : ℝ) ^ (1 - (3666565558019 : ℝ) / 10 ^ 17))) at hj
  change MulTimeBound (fun n : ℕ =>
    (n : ℝ) * ((lg n : ℝ) ^ (1 - (1 : ℝ) / 2 ^ 182)))
  rcases hj with ⟨M, hcorrect, c, hc, n₀, hcost⟩
  refine ⟨M, hcorrect, c, hc, n₀, ?_⟩
  intro n hn₀ hn₁
  intro x y hx hy
  obtain ⟨t, ht, houtput⟩ := hcost n hn₀ hn₁ x y hx hy
  refine ⟨t, ?_, houtput⟩
  have hκ :
      (1 : ℝ) / 2 ^ 182 ≤ (3666565558019 : ℝ) / 10 ^ 17 := by
    norm_num
  have hlg_nat : 1 ≤ lg n := by
    exact le_max_right (Nat.clog 2 n) 1
  have hlg : (1 : ℝ) ≤ (lg n : ℝ) := by
    exact_mod_cast hlg_nat
  have hrpow :
      (lg n : ℝ) ^ (1 - (3666565558019 : ℝ) / 10 ^ 17) ≤
      (lg n : ℝ) ^ (1 - (1 : ℝ) / 2 ^ 182) := by
    apply Real.rpow_le_rpow_of_exponent_le hlg
    linarith
  have hscaled :
      c * ((n : ℝ) *
        ((lg n : ℝ) ^ (1 - (3666565558019 : ℝ) / 10 ^ 17))) ≤
      c * ((n : ℝ) *
        ((lg n : ℝ) ^ (1 - (1 : ℝ) / 2 ^ 182))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hrpow (Nat.cast_nonneg n)) hc.le
  exact ht.trans hscaled
