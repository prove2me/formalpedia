-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T03:09:49.921256+00:00
-- url     : https://prove2.me/submissions/0a8be72c-edb9-41d8-9e86-a40753cf726f

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators Pointwise

theorem solution (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ a}).toReal =
      a ^ m * (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1}).toReal := by
  classical
  have hdil :
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ a} =
        a • {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1} := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      apply Set.mem_smul_set.mpr
      by_cases ha0 : a = 0
      · have hx0 : x = 0 := by
          funext i
          have hxi : x i ≤ 0 := by
            calc
              x i ≤ ∑ j : Fin m, x j :=
                Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
              _ ≤ 0 := by simpa only [ha0] using hx.2
          exact le_antisymm hxi (hx.1 i)
        refine ⟨0, ?_, ?_⟩
        · simp
        · simpa only [smul_zero] using hx0.symm
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        refine ⟨(fun i => x i / a), ⟨?_, ?_⟩, ?_⟩
        · intro i
          exact div_nonneg (hx.1 i) ha
        · rw [← Finset.sum_div]
          exact (div_le_one hapos).2 hx.2
        · funext i
          change a * (x i / a) = x i
          exact mul_div_cancel₀ (x i) ha0
    · intro hx
      rcases Set.mem_smul_set.mp hx with ⟨y, hy, hxy⟩
      rw [← hxy]
      constructor
      · intro i
        change 0 ≤ a * y i
        exact mul_nonneg ha (hy.1 i)
      · change (∑ i : Fin m, a * y i) ≤ a
        rw [← Finset.mul_sum]
        calc
          a * (∑ i : Fin m, y i) ≤ a * 1 := mul_le_mul_of_nonneg_left hy.2 ha
          _ = a := mul_one a
  rw [hdil, MeasureTheory.Measure.addHaar_smul_of_nonneg MeasureTheory.volume ha]
  simp only [Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha m)]
