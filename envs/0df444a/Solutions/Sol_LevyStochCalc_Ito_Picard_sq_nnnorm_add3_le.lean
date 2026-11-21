-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.sq_nnnorm_add3_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:41:26.739+00:00
-- url     : https://prove2.me/submissions/8f9da559-4be7-4a3c-86c9-c289d8bd2fa3

import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the Picard step

Each of the three components of the Picard step — the Lebesgue drift integral, the Brownian
stochastic integral and the compensated jump integral — is bounded in `L²` uniformly over
`[0, T]` by the energies of its integrand, through Cauchy–Schwarz for the drift and the Itô
and Itô–Lévy isometries for the two stochastic components; summing the three bounds gives a
finite Bielecki norm for the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]




theorem _root_.solution (x y z : ℝ) :
    (‖x + y + z‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
  have h : (x + y + z) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  have hr : ((‖x + y + z‖₊ : ℝ≥0) : ℝ) ^ 2 ≤
      3 * ((‖x‖₊ : ℝ≥0) : ℝ) ^ 2 + 3 * ((‖y‖₊ : ℝ≥0) : ℝ) ^ 2 +
      3 * ((‖z‖₊ : ℝ≥0) : ℝ) ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using h
  have hn : ‖x + y + z‖₊ ^ 2 ≤ 3 * ‖x‖₊ ^ 2 + 3 * ‖y‖₊ ^ 2 + 3 * ‖z‖₊ ^ 2 := by
    exact_mod_cast hr
  exact_mod_cast hn
