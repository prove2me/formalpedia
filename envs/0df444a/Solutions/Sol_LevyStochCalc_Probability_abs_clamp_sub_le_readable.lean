-- Prove2me | solution 1 for LevyStochCalc.Probability.abs_clamp_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:42.408993+00:00
-- url     : https://prove2.me/submissions/6c41a0a0-2a50-48eb-8415-fd7a6cf6a4b6

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]
/-- Clamping to `[0, t]` does not increase the distance to a point of `[0, t]`. -/
theorem solution {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (x : ℝ) :
    |max 0 (min t x) - s| ≤ |x - s| := by
  obtain ⟨hs0, hst⟩ := hs
  rcases lt_or_ge x 0 with hx | hx
  · rw [min_eq_right (hx.le.trans ht), max_eq_left hx.le,
      abs_of_nonpos (by linarith : (0 : ℝ) - s ≤ 0), abs_of_nonpos (by linarith : x - s ≤ 0)]
    linarith
  · rcases lt_or_ge t x with hxt | hxt
    · rw [min_eq_left hxt.le, max_eq_right ht,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - s)]
      linarith
    · rw [min_eq_right hxt, max_eq_right hx]
