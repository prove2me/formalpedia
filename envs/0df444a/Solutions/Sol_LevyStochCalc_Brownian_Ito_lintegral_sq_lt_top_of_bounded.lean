-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_sq_lt_top_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:46:37.565967+00:00
-- url     : https://prove2.me/submissions/bef69a38-4454-4abc-89f3-9744fd2da704

import Definitions.Def_LevyStochCalc_Analysis_ScaledTrig_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for the scaled cosine and sine of a Brownian increment

`x ↦ cos (l * x)` and `x ↦ sin (l * x)` satisfy the hypotheses of Itô's formula for a scalar Itô
process, so for a version of `∫ 1_{(a,b]} dW` they give

  `cos (l * X_T) − cos (l * X_0) = ∫ (−l sin (l X)) 1_{(a,b]} dW − (l²/2) ∫ cos (l X) 1_{(a,b]} ds`

and the companion identity for the sine.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |F ω s| ≤ M) (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  let C : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hbound (ω : Ω) (s : ℝ) : ‖F ω s‖₊ ≤ C := by
    change (‖F ω s‖₊ : ℝ) ≤ max M 0
    simpa only [coe_nnnorm, Real.norm_eq_abs] using (hM ω s).trans (le_max_left _ _)
  calc
    _ ≤ ∫⁻ _ : Ω, ∫⁻ _ in Set.Icc (0 : ℝ) T, (C : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      apply lintegral_mono
      intro ω
      apply lintegral_mono
      intro s
      exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr (hbound ω s)) 2
    _ < ⊤ := by
      rw [lintegral_const, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
      simp only [measure_univ, mul_one]
      exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
