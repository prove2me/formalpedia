-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.analyticColumn_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:21:42.23961+00:00
-- url     : https://prove2.me/submissions/3e1d9c20-c6e4-4aca-bc54-d58a52c37c25

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_unweighted_factor_bound

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ) (w : Fin m → ℝ)
    {R wstar : ℝ}
    (hR : 1 ≤ R) (hws : 0 < wstar) (hw : ∀ i, wstar ≤ w i)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp ((h : ℝ) * R +
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar) := by
  have hunweighted :=
    OAI.PiExponent.FinitePeriodCollision.analyticColumn_unweighted_factor_bound
      h a A hR hz
  have hsum : (∑ i, (a i : ℝ)) ≤ (∑ i, w i * (a i : ℝ)) / wstar := by
    rw [le_div_iff₀' hws]
    calc
      wstar * (∑ i, (a i : ℝ)) = ∑ i, wstar * (a i : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ∑ i, w i * (a i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg (a i))
  have hlog : 0 ≤ Real.log (2 * R) := by
    apply Real.log_nonneg
    nlinarith [hR]
  have hcompare :
      (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar := by
    calc
      (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
          ((∑ i, w i * (a i : ℝ)) / wstar) * Real.log (2 * R) :=
        mul_le_mul_of_nonneg_right hsum hlog
      _ = (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar := by ring
  exact hunweighted.trans (Real.exp_le_exp.mpr (add_le_add (le_refl ((h : ℝ) * R)) hcompare))