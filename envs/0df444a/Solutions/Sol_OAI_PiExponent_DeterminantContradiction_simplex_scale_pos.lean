-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_scale_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:35:49.528702+00:00
-- url     : https://prove2.me/submissions/bb2472b1-bcab-47cc-94a5-ef2f698f08c2

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators Pointwise

theorem solution (k : ℕ) (U : ℝ) (hU : 0 < U) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U}).toReal =
      (U ^ k) * (MeasureTheory.volume
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal := by
  classical
  have hImage :
      (fun x : Fin k → ℝ => U • x) ''
          {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1} =
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (∀ i, 0 ≤ U * x i) ∧ (∑ i : Fin k, U * x i) ≤ U
      constructor
      · intro i
        exact mul_nonneg hU.le (hx.1 i)
      · rw [← Finset.mul_sum]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2 hU.le
    · intro hy
      refine ⟨(fun i => y i / U), ?_, ?_⟩
      · constructor
        · intro i
          exact div_nonneg (hy.1 i) hU.le
        · rw [← Finset.sum_div]
          exact (div_le_iff₀ hU).2 (by simpa only [one_mul] using hy.2)
      · funext i
        change U * (y i / U) = y i
        exact mul_div_cancel₀ _ hU.ne'
  rw [← hImage]
  change (MeasureTheory.volume
      (U • {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1})).toReal = _
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg
    (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) hU.le]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hU.le k)]