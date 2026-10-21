-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.analyticColumn_binomial_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:41:37.549988+00:00
-- url     : https://prove2.me/submissions/fba16f6a-8fd8-4578-8449-46b376b4960d

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_binomial_choose_exp_bound
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_binomial_exp_product_bound

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (a A : Fin m → ℕ) :
    ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ ≤
      Real.exp ((∑ i, (a i : ℝ)) * Real.log 2) := by
  let x : Fin m → ℝ := fun i => (((a i).choose (A i) : ℕ) : ℝ)
  let b : Fin m → ℝ := fun i => (a i : ℝ) * Real.log 2
  have hx : ∀ i, 0 ≤ x i := by
    intro i
    simp [x]
  have hfactor : ∀ i, x i ≤ Real.exp (b i) := by
    intro i
    simpa [x, b, mul_comm] using
      OAI.PiExponent.FinitePeriodCollision.binomial_choose_exp_bound
        (a i) (A i)
  have hprod :=
    OAI.PiExponent.FinitePeriodCollision.binomial_exp_product_bound x b hx hfactor
  simpa [x, b, Finset.sum_mul] using hprod