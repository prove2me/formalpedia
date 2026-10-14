-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.log_tail_coeff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T13:45:53.546985+00:00
-- url     : https://prove2.me/submissions/153456c9-e78e-414d-8bc4-b3769960af80

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic

theorem solution (T n : ℕ) :
    ‖PowerSeries.coeff n (RowTranslation.tail T (PowerSeries.log ℂ))‖ ≤ 1 ∧
      (n < T → PowerSeries.coeff n (RowTranslation.tail T (PowerSeries.log ℂ)) = 0) := by
  constructor
  · rw [RowTranslation.tail, map_sub]
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    by_cases h : n < T
    · simp [h]
    · simp only [if_neg h, zero_sub]
      by_cases hn : n = 0
      · simp [hn]
      · rw [norm_neg]
        rw [PowerSeries.coeff_log, if_neg hn]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hnormRat : ‖((-1 : ℚ) ^ (n + 1) / n : ℚ)‖ ≤ 1 := by
          change |(((-1 : ℚ) ^ (n + 1) / n : ℚ) : ℝ)| ≤ 1
          push_cast
          rw [abs_div, abs_pow, abs_neg, abs_one, one_pow]
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
          exact div_le_one_of_le₀ (by exact_mod_cast hnpos) (by positivity)
        have hnorm : ‖algebraMap ℚ ℂ ((-1 : ℚ) ^ (n + 1) / n)‖ ≤ 1 := by
          simpa only [norm_algebraMap'] using hnormRat
        exact hnorm
  · intro h
    rw [RowTranslation.tail, map_sub]
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    simp [h]
