-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:55:47.352861+00:00
-- url     : https://prove2.me/submissions/c3c0fc97-199a-448d-8ea1-915e392cc031

import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
The tail of the formal logarithm has zero coefficients before the strict
truncation cutoff, and coefficients at most one in complex norm.
-/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (T : ℕ) (hT : 1 ≤ T) :
    (∀ n, n < T →
      PowerSeries.coeff n
        ((PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ) = 0) ∧
    (∀ n, ‖PowerSeries.coeff n
        ((PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ)‖ ≤ 1) := by
  constructor
  · intro n hn
    rw [map_sub]
    simp [PowerSeries.coeff_trunc, hn]
  · intro n
    rw [map_sub]
    by_cases hn : n < T
    · simp [PowerSeries.coeff_trunc, hn]
    · have htrunc : PowerSeries.coeff n
          ((PowerSeries.trunc T (PowerSeries.log ℂ) : Polynomial ℂ) : PowerSeries ℂ) = 0 := by
        simp [PowerSeries.coeff_trunc, hn]
      rw [htrunc]
      simp only [zero_sub]
      have hn0 : n ≠ 0 := by
        intro hnz
        subst n
        exact hn (lt_of_lt_of_le Nat.zero_lt_one hT)
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hcoeff : PowerSeries.coeff n (PowerSeries.log ℂ) =
          (-1 : ℂ) ^ (n + 1) / (n : ℂ) := by
        simp [PowerSeries.coeff_log, hn0]
      rw [hcoeff]
      have hnR : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.succ_le_of_lt hnpos)
      have hnRpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
      calc
        ‖-(((-1 : ℂ) ^ (n + 1)) / (n : ℂ))‖ = 1 / (n : ℝ) := by
          simp [norm_div, norm_pow, Complex.norm_natCast]
        _ ≤ 1 := (div_le_one₀ hnRpos).2 hnR
