-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:21.530951+00:00
-- url     : https://prove2.me/submissions/a1c709e9-5d9e-443a-9a84-03b966e7ec07

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoRiemannIntegrand

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoRiemannIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Comparison
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ in
/-- **Replacing the weight costs the `L²` distance between the weights.** -/
theorem solution
    (u v : Ω → ℝ → ℝ)
    (hmu : Measurable (Function.uncurry fun ω s => u ω s * H ω s))
    (hpu : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => u ω s * H ω s)
    (hqu : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖u ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmv : Measurable (Function.uncurry fun ω s => v ω s * H ω s))
    (hpv : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => v ω s * H ω s)
    (hqv : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖v ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => u ω s * H ω s) hmu hpu hqu T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => v ω s * H ω s) hmv hpv hqv T ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian W ℱ hℱ _ _ hmu hmv hpu hpv hqu hqv hT]
  rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (C ^ 2) ≠ ⊤)]
  refine lintegral_mono fun ω => ?_
  rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (C ^ 2) ≠ ⊤)]
  refine lintegral_mono fun s => ?_
  have hfac : u ω s * H ω s - v ω s * H ω s = (u ω s - v ω s) * H ω s := by ring
  rw [hfac]
  have hnn : (‖(u ω s - v ω s) * H ω s‖₊ : ℝ≥0∞) ^ 2
      = (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
  rw [hnn, mul_comm (ENNReal.ofReal (C ^ 2))]
  refine mul_le_mul_right ?_ _
  have h1 : (‖H ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C := by
    rw [ENNReal.ofReal_eq_coe_nnreal hC0]
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using hCH ω s
  calc (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal C ^ 2 := pow_le_pow_left' h1 2
    _ = ENNReal.ofReal (C ^ 2) := (ENNReal.ofReal_pow hC0 2).symm
