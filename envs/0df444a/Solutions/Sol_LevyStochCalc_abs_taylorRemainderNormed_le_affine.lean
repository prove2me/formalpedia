-- Prove2me | solution 1 for LevyStochCalc.abs_taylorRemainderNormed_le_affine
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:48:26.208177+00:00
-- url     : https://prove2.me/submissions/0591f1ab-f6bd-4254-8553-f8686e5947d2

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwoModulus_F000

namespace LevyStochCalc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem _root_.solution {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x : ℕ → E) (m : ℕ) :
    |taylorRemainderNormed f f' f'' x m|
      ≤ A * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 2
        + K * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 3 := by
  have e : taylorRemainderNormed f f' f'' x m
      = ∑ i ∈ Finset.range m, (f (x (i + 1)) - f (x i) - f' (x i) (x (i + 1) - x i)
          - f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2) := by
    unfold taylorRemainderNormed
    rw [← Finset.sum_range_sub (fun i => f (x i)) m]
    simp only [Finset.sum_sub_distrib]
    ring
  rw [e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact abs_sub_taylor_two_le_affine hA0 hK0 hf hf' hf'' (x i) (x (i + 1))

end LevyStochCalc
