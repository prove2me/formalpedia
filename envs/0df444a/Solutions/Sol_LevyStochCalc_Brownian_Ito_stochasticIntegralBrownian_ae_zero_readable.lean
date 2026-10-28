-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:46.124991+00:00
-- url     : https://prove2.me/submissions/ece5a26e-19f8-40e4-b677-ae96295a46d0

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoZero

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoZero.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- **The Itô integral of the zero integrand vanishes almost surely.** -/
theorem solution
    (hm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ))
    (hq : ∀ T, 0 < T → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t =ᵐ[P] 0 := by
  rcases le_or_gt t 0 with ht | ht
  · exact LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ _ hm hp hq ht
  · have hiso := LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq ht
    have hrhs : ∫⁻ ω, ∫⁻ _s in Set.Icc (0 : ℝ) t,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
      simp
    rw [hrhs] at hiso
    have hmeas : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun _ _ => (0 : ℝ)) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2) P :=
      ((((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ _ hm hp hq t).mono
        (ℱ.le t)).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable
    have hzero := (MeasureTheory.lintegral_eq_zero_iff' hmeas).mp hiso
    filter_upwards [hzero] with ω hω
    have : (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t ω‖₊ : ℝ≥0∞) = 0 := by
      simpa [pow_eq_zero_iff] using hω
    simpa using this
