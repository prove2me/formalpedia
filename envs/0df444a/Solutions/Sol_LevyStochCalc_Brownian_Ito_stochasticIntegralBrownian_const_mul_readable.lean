-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_const_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:06:13.451981+00:00
-- url     : https://prove2.me/submissions/63bacde8-fc96-434e-941e-075b8b6ba962

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_eq_const_mul_of_sq_distances_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_const_mul_readable

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
section Scaling
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- **The L² Itô integral commutes with scaling of the integrand.** -/
theorem solution {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (c : ℝ)
    (hmc : Measurable (Function.uncurry fun ω s => c * H ω s))
    (hpc : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => c * H ω s)
    (hqc : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc T
      =ᵐ[P] fun ω => c * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω := by
  have hscale := LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul_readable (P := P) hm c T
  have hdiff : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖c * H ω s - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal ((c - 1) ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    refine Eq.trans ?_ (LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul_readable (P := P) hm (c - 1) T)
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf
  refine LevyStochCalc.Brownian.Ito.ae_eq_const_mul_of_sq_distances_readable
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc T)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq T)
    (LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc hT)
    (LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ H hm hp hq hT)
    (LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) H hmc hm hpc hp
      hqc hq hT) ?_ ?_
  · rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c)]
  · rw [hdiff, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (c - 1))]
