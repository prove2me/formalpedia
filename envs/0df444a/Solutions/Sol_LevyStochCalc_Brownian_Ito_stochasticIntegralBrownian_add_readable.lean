-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:12.82468+00:00
-- url     : https://prove2.me/submissions/e76e3368-7d13-4a83-a7d6-1b18c785cc30

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_eq_add_of_sq_distances_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_lt_top_of_bound_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_parallelogram_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- The squared extended norm of a real number is the extended real of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq (z : ℝ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The squared extended norm of a difference is dominated by twice the sum of the squares. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul (x y : ℝ) :
    (‖x - y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x + y)])
end Energy
section Additivity
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- **Additivity of the L² Itô integral in the integrand.** -/
theorem solution {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
    (hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
    (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa T
      =ᵐ[P] fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
        + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω := by
  have hqd : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound_readable (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hm₁ hm₂ hq₁ hq₂
  refine LevyStochCalc.Brownian.Ito.ae_eq_add_of_sq_distances_readable
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₁ hm₁ hp₁ hq₁ T)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₂ hm₂ hp₂ hq₂ T)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa T)
    (hq₁ T hT).ne (hq₂ T hT).ne (hqa T hT).ne (hqd T hT).ne
    (LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ hT)
    (LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ hT)
    (LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa hT)
    ?_ ?_
    (LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hT)
    (LevyStochCalc.Brownian.Ito.lintegral_energy_parallelogram_readable (P := P) hm₁ hm₂ T)
  · refine Eq.trans (LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => H₁ ω s + H₂ ω s) H₁ hma hm₁ hpa hp₁ hqa hq₁ hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf
  · refine Eq.trans (LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => H₁ ω s + H₂ ω s) H₂ hma hm₂ hpa hp₂ hqa hq₂ hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf
