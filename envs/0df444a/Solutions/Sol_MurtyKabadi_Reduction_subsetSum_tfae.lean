-- Prove2me | solution 1 for MurtyKabadi.Reduction.subsetSum_tfae
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T08:13:54.467686+00:00
-- url     : https://prove2.me/submissions/43740a67-4163-4070-991b-88dd0194c634

import Theorems.Thm_MurtyKabadi_Reduction_problems5_6_equiv
import Theorems.Thm_MurtyKabadi_Reduction_problems6_7_equiv
import Theorems.Thm_MurtyKabadi_Reduction_problems7_8_equiv
import Theorems.Thm_MurtyKabadi_Reduction_problems8_9_equiv
import Theorems.Thm_MurtyKabadi_Reduction_problem9_special_case_problem4
import Theorems.Thm_MurtyKabadi_Reduction_problems3_4_equiv
import Theorems.Thm_MurtyKabadi_Reduction_problems1_2_equiv_problem3
import Theorems.Thm_MurtyKabadi_Reduction_problems11_12_equiv

open MurtyKabadi.Reduction

theorem solution {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ)
    (hε0 : 0 < ε) (hε : ε * (2 : ℚ) ^ (n * digitCount d d0 ^ 2) < 1) :
    List.TFAE
      [SubsetSumSolvable d d0,
       Problem1 (mkMatrix d d0 δ ε),
       Problem2 (mkMatrix d d0 δ ε),
       Problem3 (mkMatrix d d0 δ ε),
       ¬ Copositive (mkMatrix d d0 δ ε),
       Problem4 (mkMatrix d d0 δ ε) n,
       Problem11 (mkMatrix d d0 δ ε),
       Problem12 (mkMatrix d d0 δ ε)] := by
  classical
  tfae_have 2 ↔ 4 := (problems1_2_equiv_problem3 (mkMatrix d d0 δ ε)).1
  tfae_have 3 ↔ 4 := (problems1_2_equiv_problem3 (mkMatrix d d0 δ ε)).2
  tfae_have 7 ↔ 2 := (problems11_12_equiv (mkMatrix d d0 δ ε)).1
  tfae_have 8 ↔ 3 := (problems11_12_equiv (mkMatrix d d0 δ ε)).2
  tfae_have 4 ↔ 5 := by
    simp only [Problem3, Copositive, not_forall, not_le, exists_prop]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- In dimension zero the subset sum and negative-witness questions are false.
    have hd0z : (d0 : ℤ) ≠ 0 := by exact_mod_cast hd0.ne'
    tfae_have 1 ↔ 4 := by
      simp [SubsetSumSolvable, Problem3, Q, dotProduct, hd0z.symm]
    tfae_have 4 ↔ 6 := by
      simp [Problem3, Problem4, Q, dotProduct]
    tfae_finish
  · -- Compose the source's Problems 5 → 6 → 7 → 8 → 9 → 4.
    tfae_have 1 ↔ 6 :=
      (problems5_6_equiv d d0 δ hd hd0 hδ).trans
        ((problems6_7_equiv d d0 δ hd hd0 hδ).trans
          ((problems7_8_equiv hn d d0 δ hd hd0 hδ).trans
            ((problems8_9_equiv hn d d0 δ ε hd hd0 hδ hε0 hε).trans
              (problem9_special_case_problem4 d d0 δ ε).2)))
    tfae_have 4 ↔ 6 :=
      problems3_4_equiv (mkMatrix d d0 δ ε) n (by exact_mod_cast hn)
    tfae_finish
