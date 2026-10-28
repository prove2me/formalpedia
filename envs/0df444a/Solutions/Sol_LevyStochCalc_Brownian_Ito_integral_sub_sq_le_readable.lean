-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sub_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:04.155365+00:00
-- url     : https://prove2.me/submissions/3d6f4b31-70d4-4421-95a4-1185913f0763

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_sub_sq_le_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A measurable function with finite `lintegral` of its norm is integrable. -/
theorem LevyStochCalc.Brownian.Ito.integrable_of_lintegral_nnnorm_lt_top {P : Measure Ω} {f : Ω → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f P)
    (h : ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ∂P < ⊤) : MeasureTheory.Integrable f P := by
  refine ⟨hf, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  simpa only [enorm_eq_nnnorm] using h
/-- A pointwise-nonnegative integrand is bounded through its `lintegral`. -/
theorem LevyStochCalc.Brownian.Ito.integral_le_of_lintegral_ofReal_le {P : Measure Ω} {f : Ω → ℝ}
    (hint : MeasureTheory.Integrable f P) (hnn : ∀ ω, 0 ≤ f ω) {K : ℝ} (hK : 0 ≤ K)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal K) : ∫ ω, f ω ∂P ≤ K := by
  rw [← ENNReal.ofReal_le_ofReal_iff hK,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  exact h
section ThirdMoment
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ in
/-- The increment of the `L²` Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian (a b : ℝ) :
    Measurable fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
  (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
      (ℱ.le b)).measurable).sub
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
      (ℱ.le a)).measurable)
include hℱ hC0 hCH in
/-- The square of an increment is integrable, with the second-moment bound. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) P
      ∧ ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 ∂P
        ≤ C ^ 2 * (b - a) := by
  have hmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq a b
  have hbound := LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_sq_le_readable W ℱ hℱ H hm hp hq
    hC0 hCH ha hab
  have hpt : ∀ ω : Ω, ENNReal.ofReal ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2)
      = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 := by
    have key : ∀ x : ℝ, ENNReal.ofReal (x ^ 2) = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
      intro x
      have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
        rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
        exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
      rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
    exact fun ω => key _
  have hnn : ∀ ω : Ω, (0 : ℝ) ≤ (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 := fun ω => by positivity
  have hint : MeasureTheory.Integrable
      (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) P := by
    refine LevyStochCalc.Brownian.Ito.integrable_of_lintegral_nnnorm_lt_top
      (hmeas.pow_const 2).aestronglyMeasurable ?_
    have hrw : ∀ ω : Ω, ((‖(LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2‖₊ : ℝ≥0∞))
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω
      rw [nnnorm_pow, ENNReal.coe_pow]
    simp_rw [hrw]
    exact lt_of_le_of_lt hbound (by simp)
  refine ⟨hint, LevyStochCalc.Brownian.Ito.integral_le_of_lintegral_ofReal_le hint hnn (by positivity) ?_⟩
  simp_rw [hpt]
  exact hbound
