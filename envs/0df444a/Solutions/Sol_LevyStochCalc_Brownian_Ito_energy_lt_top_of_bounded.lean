-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:46:37.494107+00:00
-- url     : https://prove2.me/submissions/35d22f1a-4ab1-4754-bc98-b948754368b6

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

end Cutoff

namespace Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Bounded

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]



theorem _root_.solution {K : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |K ω s| ≤ M) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  let C : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hbound (ω : Ω) (s : ℝ) : ‖K ω s‖₊ ≤ C := by
    change (‖K ω s‖₊ : ℝ) ≤ max M 0
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
