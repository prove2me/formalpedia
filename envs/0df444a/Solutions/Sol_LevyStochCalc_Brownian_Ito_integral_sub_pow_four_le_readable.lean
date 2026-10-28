-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sub_pow_four_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:25.991166+00:00
-- url     : https://prove2.me/submissions/b18dc08e-e6c9-46c7-bd2c-8b855878f586

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_sub_pow_four_le_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg fun x => by positivity
end
end

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
/-- The fourth power of an increment is integrable, with the fourth-moment bound. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) P
      ∧ ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 ∂P
        ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by
  have hmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq a b
  have hbound := LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_pow_four_le_readable W ℱ hℱ H hm hp hq
    hC0 hCH ha hab
  have hpt : ∀ ω : Ω, ENNReal.ofReal ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4)
      = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
    have key : ∀ x : ℝ, ENNReal.ofReal (x ^ 4) = (‖x‖₊ : ℝ≥0∞) ^ 4 := by
      intro x
      have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
        rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
        exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
      rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
    exact fun ω => key _
  have hnn : ∀ ω : Ω, (0 : ℝ) ≤ (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 := fun ω => by positivity
  have hint : MeasureTheory.Integrable
      (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) P := by
    refine LevyStochCalc.Brownian.Ito.integrable_of_lintegral_nnnorm_lt_top
      (hmeas.pow_const 4).aestronglyMeasurable ?_
    have hrw : ∀ ω : Ω, ((‖(LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4‖₊ : ℝ≥0∞))
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
      intro ω
      rw [nnnorm_pow, ENNReal.coe_pow]
    simp_rw [hrw]
    exact lt_of_le_of_lt hbound (by simp)
  have hKnn : (0 : ℝ) ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith [LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg]) (by positivity))
      (by positivity)
  refine ⟨hint, LevyStochCalc.Brownian.Ito.integral_le_of_lintegral_ofReal_le hint hnn hKnn ?_⟩
  simp_rw [hpt]
  exact hbound
