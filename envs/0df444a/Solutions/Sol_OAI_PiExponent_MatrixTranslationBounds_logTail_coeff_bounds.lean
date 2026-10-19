-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.logTail_coeff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:19:33.749179+00:00
-- url     : https://prove2.me/submissions/2fbf0bac-38f5-4575-badd-ee77dd840204

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators
open OAI.PiExponent.RowTranslation

theorem solution (T : ℕ) :
    PowerSeries.coeff 0 (tail T (PowerSeries.log ℂ)) = 0 ∧
      ∀ n, ‖PowerSeries.coeff n (tail T (PowerSeries.log ℂ))‖ ≤ (1 : ℝ) := by
  have htail (n : ℕ) :
      PowerSeries.coeff n (tail T (PowerSeries.log ℂ)) =
        if n < T then 0 else -PowerSeries.coeff n (PowerSeries.log ℂ) := by
    dsimp only [tail]
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    by_cases h : n < T <;> simp [h]
  have hlog (n : ℕ) : ‖PowerSeries.coeff n (PowerSeries.log ℂ)‖ ≤ (1 : ℝ) := by
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hnorm : ‖PowerSeries.coeff n (PowerSeries.log ℂ)‖ = 1 / (n : ℝ) := by
        rw [PowerSeries.coeff_log, if_neg hn]
        simp only [map_div₀, map_pow, map_neg, map_one, map_natCast,
          norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
      rw [hnorm]
      simpa only [div_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1)
  constructor
  · rw [htail 0]
    split_ifs <;> simp
  · intro n
    rw [htail n]
    split_ifs
    · simp
    · simpa only [norm_neg] using hlog n