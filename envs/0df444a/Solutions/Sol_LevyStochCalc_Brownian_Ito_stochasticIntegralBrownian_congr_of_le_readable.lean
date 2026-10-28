-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:24.977071+00:00
-- url     : https://prove2.me/submissions/7b0a41f4-5b75-47ed-a24f-4522a3f3610c

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_congr_of_pos_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_stopped_eq_of_le_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)
section Local
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
/-- **Two integrands agreeing up to a stopping time have the same integral at a time that
stopping time has not reached.** -/
theorem solution
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ ω → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  classical
  have e1 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le_readable τ W ℱ hℱ hτ hm₁ hp₁ hq₁ ht
  have e2 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le_readable τ W ℱ hℱ hτ hm₂ hp₂ hq₂ ht
  have hstop : ∀ (ω : Ω) (s : ℝ), 0 < s →
      LevyStochCalc.Probability.stopped τ H₁ ω s = LevyStochCalc.Probability.stopped τ H₂ ω s := by
    intro ω s hs
    unfold LevyStochCalc.Probability.stopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [if_pos hle, if_pos hle, hagree ω s hs hle]
    · rw [if_neg hle, if_neg hle]
  have e3 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos_readable W ℱ hℱ
    (LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm₁)
    (LevyStochCalc.Probability.ProgressivelyMeasurable.stopped hτ hp₁)
    (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H₁ ω s) hq₁)
    (LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm₂)
    (LevyStochCalc.Probability.ProgressivelyMeasurable.stopped hτ hp₂)
    (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H₂ ω s) hq₂)
    hstop ht
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]
