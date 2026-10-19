-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:16:32.411767+00:00
-- url     : https://prove2.me/submissions/6e0d2fca-7f62-4ec0-a80f-42dbf9ea8976

import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_logTail_product_coefficient_control_generic_product
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_logTail_product_coefficient_control_log_tail

open scoped BigOperators

theorem solution
    {m : ℕ} (T b : Fin m → ℕ) (k : ℕ) (hT : ∀ i, 1 ≤ T i) :
    ‖PowerSeries.coeff k
      (∏ i : Fin m,
        ((PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ) ^ b i)‖ ≤ (2 : ℝ) ^ k ∧
    (PowerSeries.coeff k
      (∏ i : Fin m,
        ((PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ) ^ b i) ≠ 0 →
      ∑ i : Fin m, T i * b i ≤ k) := by
  exact OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_generic_product
    (f := fun i => (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) -
      PowerSeries.log ℂ)
    T b k hT
    (fun i n hn =>
      (OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_log_tail
        (T i) (hT i)).1 n hn)
    (fun i n =>
      (OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_log_tail
        (T i) (hT i)).2 n)