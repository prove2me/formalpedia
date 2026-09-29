-- Prove2me | solution 1 for MurtyKabadi.Reduction.problems3_4_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:22:55.768754+00:00
-- url     : https://prove2.me/submissions/0d9a3bb9-ac46-442e-9831-1afbdb60ae82

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

open MurtyKabadi.Reduction

private theorem Q_smul {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) :
    Q D (c • v) = c ^ 2 * Q D v := by
  simp only [Q, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hin : ∑ j, D i j * (c * v j) = c * ∑ j, D i j * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hin]
  ring

private theorem Q_zero {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Q D 0 = 0 := by
  simp [Q, Matrix.mulVec, dotProduct]

theorem solution {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (a0 : ℝ) (ha0 : 0 < a0) :
    Problem3 D ↔ Problem4 D a0 := by
  constructor
  · rintro ⟨x, hxnn, hxneg⟩
    -- the coordinate sum is positive, since `x = 0` would give `Q x = 0`
    have hs0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hxnn i
    have hspos : 0 < ∑ i, x i := by
      rcases eq_or_lt_of_le hs0 with heq | hlt
      · exfalso
        have hall : ∀ i ∈ (Finset.univ : Finset ι), x i = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hxnn i).mp heq.symm
        have hx0 : x = 0 := funext fun i => hall i (Finset.mem_univ i)
        rw [hx0, Q_zero] at hxneg
        exact absurd hxneg (lt_irrefl 0)
      · exact hlt
    refine ⟨(a0 / ∑ i, x i) • x, ?_, smul_nonneg (by positivity) hxnn, ?_⟩
    · have : ∑ i, ((a0 / ∑ i, x i) • x) i = (a0 / ∑ i, x i) * ∑ i, x i := by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
      rw [this, div_mul_cancel₀]
      exact ne_of_gt hspos
    · rw [Q_smul]
      have hcpos : 0 < (a0 / ∑ i, x i) ^ 2 := by positivity
      exact mul_neg_of_pos_of_neg hcpos hxneg
  · rintro ⟨x, _, hxnn, hxneg⟩
    exact ⟨x, hxnn, hxneg⟩
