-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_region_eq_smul_image
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:33:23.068749+00:00
-- url     : https://prove2.me/submissions/dc00aef2-86c5-47e8-9d20-498880c22d38

import Mathlib

open scoped BigOperators Topology

theorem solution
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T} =
      (fun x : Fin m → ℝ => T • x) ''
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)} := by
  classical
  ext x
  constructor
  · rintro ⟨hx_nonneg, hx_sum⟩
    by_cases hT0 : T = 0
    · have hx_zero : x = 0 := by
        funext i
        have hxi_sum : x i ≤ ∑ j : Fin m, x j :=
          Finset.single_le_sum (fun j hj => hx_nonneg j) (Finset.mem_univ i)
        have hxi_le : x i ≤ 0 := by
          simpa [hT0] using hxi_sum.trans hx_sum
        exact le_antisymm hxi_le (hx_nonneg i)
      refine ⟨0, ?_, ?_⟩
      · constructor
        · intro i
          simp
        · simp
      · funext i
        simp [hT0, hx_zero]
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      let y : Fin m → ℝ := fun i => x i / T
      refine ⟨y, ?_, ?_⟩
      · constructor
        · intro i
          exact div_nonneg (hx_nonneg i) hT
        · calc
            ∑ i : Fin m, y i = (∑ i : Fin m, x i) / T := by
              simp [y, Finset.sum_div]
            _ ≤ 1 := (div_le_iff₀ hTpos).2 (by simpa using hx_sum)
      · funext i
        simp [y, smul_eq_mul, mul_div_cancel₀, ne_of_gt hTpos]
  · rintro ⟨y, ⟨hy_nonneg, hy_sum⟩, hxy⟩
    subst x
    constructor
    · intro i
      exact mul_nonneg hT (hy_nonneg i)
    · calc
        ∑ i : Fin m, T * y i = T * ∑ i : Fin m, y i := by
          simp [Finset.mul_sum]
        _ ≤ T * 1 := mul_le_mul_of_nonneg_left hy_sum hT
        _ = T := mul_one T