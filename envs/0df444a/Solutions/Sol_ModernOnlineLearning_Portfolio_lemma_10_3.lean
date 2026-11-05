-- Prove2me | solution 1 for ModernOnlineLearning.Portfolio.lemma_10_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:57:46.113717+00:00
-- url     : https://prove2.me/submissions/7e3597eb-9161-4174-94d8-a0053cbb9e08

import Mathlib
set_option autoImplicit false



theorem solution {d T : ℕ} (hT : 1 ≤ T) (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsum : ∑ i, x i = (T : ℝ)) (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    ∏ i, u i ^ x i ≤ ∏ i, (x i / (T : ℝ)) ^ x i := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hu0 : ∀ i, 0 ≤ u i := hu.1
  have hu1 : ∑ i, u i = 1 := hu.2
  have hRpos : ∀ i, 0 < (x i / (T : ℝ)) ^ x i := by
    intro i
    rcases (hx i).lt_or_eq with h | h
    · exact Real.rpow_pos_of_pos (div_pos h hTpos) _
    · rw [← h]; simp
  by_cases hcase : ∃ i, 0 < x i ∧ u i = 0
  · obtain ⟨i, hxi, hui⟩ := hcase
    have : ∏ i, u i ^ x i = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hui, Real.zero_rpow hxi.ne']
    rw [this]
    exact (Finset.prod_pos fun i _ => hRpos i).le
  · push Not at hcase
    have hLpos : ∀ i, 0 < u i ^ x i := by
      intro i
      rcases (hx i).lt_or_eq with h | h
      · have : 0 < u i := lt_of_le_of_ne (hu0 i) (Ne.symm (hcase i h))
        exact Real.rpow_pos_of_pos this _
      · rw [← h]; simp
    rw [← Real.log_le_log_iff (Finset.prod_pos fun i _ => hLpos i)
      (Finset.prod_pos fun i _ => hRpos i)]
    rw [Real.log_prod (fun i _ => (hLpos i).ne'), Real.log_prod (fun i _ => (hRpos i).ne')]
    have key : ∀ i, Real.log (u i ^ x i) - Real.log ((x i / T) ^ x i) ≤ T * u i - x i := by
      intro i
      rcases (hx i).lt_or_eq with h | h
      · have hui : 0 < u i := lt_of_le_of_ne (hu0 i) (Ne.symm (hcase i h))
        rw [Real.log_rpow hui, Real.log_rpow (div_pos h hTpos), ← mul_sub,
          ← Real.log_div hui.ne' (div_pos h hTpos).ne']
        have h1 := Real.log_le_sub_one_of_pos (div_pos hui (div_pos h hTpos))
        have h2 : x i * (u i / (x i / T) - 1) = T * u i - x i := by
          field_simp
        calc x i * Real.log (u i / (x i / T)) ≤ x i * (u i / (x i / T) - 1) :=
              mul_le_mul_of_nonneg_left h1 h.le
          _ = T * u i - x i := h2
      · rw [← h]; simp
        exact mul_nonneg hTpos.le (hu0 i)
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hu1, hsum] at hs
    linarith
