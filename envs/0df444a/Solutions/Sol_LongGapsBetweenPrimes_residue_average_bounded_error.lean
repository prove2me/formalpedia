-- Prove2me | solution 1 for LongGapsBetweenPrimes.residue_average_bounded_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:04.695895+00:00
-- url     : https://prove2.me/submissions/39b6450d-590d-4d74-9302-6cade7cabaf2

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_residue_average_error
import Theorems.Thm_LongGapsBetweenPrimes_integerAverage_residue_expansion

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {m T : ℕ} (hm : 0 < m) (hT : 0 < T)
    (g : Fin m → ℝ) (hg : ∀ a, |g a| ≤ 1) :
    |integerAverage T (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) - Finset.expect Finset.univ g| ≤
      (m : ℝ) / T := by
  rw [integerAverage_residue_expansion hm, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, div_eq_mul_one_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : Fin m, |g a * ((∑ n ∈ Finset.range T, residueIndicator m a.val n) / T) -
        g a * (1 / (m : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin m, 1 / (T : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, abs_mul]
      have h := mul_le_mul (hg a) (residue_average_error a.isLt hT)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using h
    _ = (m : ℝ) / T := by simp; ring
end LongGapsBetweenPrimes
