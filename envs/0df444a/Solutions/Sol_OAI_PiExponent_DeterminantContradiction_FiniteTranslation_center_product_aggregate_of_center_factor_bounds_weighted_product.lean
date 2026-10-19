-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_weighted_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:18:53.045434+00:00
-- url     : https://prove2.me/submissions/7ede9864-9358-4199-b931-bf096133c4fc

import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

private theorem exp_pow_nat (x : ℝ) (n : ℕ) :
    Real.exp x ^ n = Real.exp (x * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

private theorem exp_prod_sum {α : Type} (s : Finset α) (f : α → ℝ) :
    (∏ i ∈ s, Real.exp (f i)) = Real.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, Real.exp_add]

theorem solution {m : ℕ} (z : Fin m → ℂ) (w : Fin m → ℝ) (e : Fin m → ℕ)
    (C nu : ℝ) (hnu : 0 ≤ nu) (hC : 0 ≤ C)
    (hcenter : ∀ i : Fin m, ‖z i‖ ≤ Real.exp (C - nu * w i)) :
    ‖∏ i : Fin m, (z i) ^ (e i)‖ ≤
      Real.exp (C * (∑ i : Fin m, (e i : ℝ)) -
        nu * (∑ i : Fin m, w i * (e i : ℝ))) := by
  have hfactor (i : Fin m) :
      ‖z i‖ ^ (e i) ≤ Real.exp ((C - nu * w i) * (e i : ℝ)) := by
    calc
      ‖z i‖ ^ (e i) ≤ Real.exp (C - nu * w i) ^ (e i) :=
        pow_le_pow_left₀ (norm_nonneg _) (hcenter i) _
      _ = Real.exp ((C - nu * w i) * (e i : ℝ)) := exp_pow_nat _ _
  calc
    ‖∏ i : Fin m, (z i) ^ (e i)‖ = ∏ i : Fin m, ‖z i‖ ^ (e i) := by simp
    _ ≤ ∏ i : Fin m, Real.exp ((C - nu * w i) * (e i : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact hfactor i
    _ = Real.exp (∑ i : Fin m, (C - nu * w i) * (e i : ℝ)) := by
      simpa using (exp_prod_sum (Finset.univ : Finset (Fin m))
        (fun i => (C - nu * w i) * (e i : ℝ)))
    _ = Real.exp (C * (∑ i : Fin m, (e i : ℝ)) -
        nu * (∑ i : Fin m, w i * (e i : ℝ))) := by
      congr 1
      simp only [Finset.sum_sub_distrib, sub_mul, ← mul_assoc, Finset.mul_sum]