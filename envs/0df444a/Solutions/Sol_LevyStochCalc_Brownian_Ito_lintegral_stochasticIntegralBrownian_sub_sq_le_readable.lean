-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:37.272138+00:00
-- url     : https://prove2.me/submissions/e0bab50d-f00a-4618-8bc5-cf91bb80b6e7

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indicator_Ioc_readable

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
section IncrementBound
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
/-- A process depending only on time is progressively measurable as soon as it is Borel. -/
theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_of_time {g : ℝ → ℝ} (hg : Measurable g) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) s => g s) := by
  intro t
  have h : Measurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
      (fun p : Ω × ℝ => (Set.Iic t).indicator g p.2) :=
    (hg.indicator measurableSet_Iic).comp measurable_snd
  exact h.stronglyMeasurable
/-- Restricting an integrand to `(a, b]` preserves joint measurability. -/
theorem LevyStochCalc.Brownian.Ito.measurable_uncurry_indicator_Ioc_mul (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H)) (a b : ℝ) :
    Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
  (((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)).mul hm
/-- Restricting an integrand to `(a, b]` preserves progressive measurability. -/
theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Ioc_mul
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (H : Ω → ℝ → ℝ)
    (hp : Probability.ProgressivelyMeasurable ℱ H) (a b : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
  (progressivelyMeasurable_of_time ℱ (measurable_const.indicator measurableSet_Ioc)).mul hp
/-- Restricting an integrand to `(a, b]` cannot increase its `L²` mass. -/
theorem LevyStochCalc.Brownian.Ito.abs_indicator_Ioc_mul_le {P : Measure Ω} [IsProbabilityMeasure P] (H : Ω → ℝ → ℝ)
    (a b : ℝ) (ω : Ω) (s : ℝ) :
    |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| := by
  by_cases hs : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem hs, one_mul]
  · rw [Set.indicator_of_notMem hs, zero_mul, abs_zero]
    exact abs_nonneg _
/-- Restricting an integrand to `(a, b]` preserves square integrability. -/
theorem LevyStochCalc.Brownian.Ito.lintegral_sq_indicator_Ioc_mul_lt_top {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Ω → ℝ → ℝ)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (a b : ℝ) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt ?_ (hq T hT)
  refine lintegral_mono fun ω => lintegral_mono fun s => ?_
  refine pow_le_pow_left' (ENNReal.coe_le_coe.mpr ?_) 2
  rw [← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_indicator_Ioc_mul_le (P := P) H a b ω s
include hℱ in
/-- **Second moment of an increment of the `L²` Itô integral.** For an integrand bounded by `C`,
`𝔼|∫_a^b H dW|² ≤ C²·(b − a)`. -/
theorem solution
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2 * (b - a)) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hFle : ∀ (ω : Ω) (s : ℝ),
      |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| :=
    fun ω s => LevyStochCalc.Brownian.Ito.abs_indicator_Ioc_mul_le (P := P) H a b ω s
  have hmF := LevyStochCalc.Brownian.Ito.measurable_uncurry_indicator_Ioc_mul H hm a b
  have hpF := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Ioc_mul ℱ H hp a b
  have hqF := LevyStochCalc.Brownian.Ito.lintegral_sq_indicator_Ioc_mul_lt_top (P := P) H hq a b
  have hloc := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_readable W ℱ hℱ H hm hp hq ha hab hmF hpF hqF hb
  rw [min_self, min_eq_left hab.le] at hloc
  have hcongr : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
          hmF hpF hqF b ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hloc] with ω hω
    rw [hω]
  rw [hcongr, LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ _ hmF hpF hqF hb]
  -- the restricted integrand has `L²` mass at most `C²(b − a)` on every path
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ENNReal.ofReal (C ^ 2 * (b - a)) := by
    intro ω
    have hptw : ∀ s : ℝ,
        (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2
          ≤ (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s := by
      intro s
      by_cases hs : s ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, one_mul]
        have h1 : (‖H ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C := by
          rw [ENNReal.ofReal_eq_coe_nnreal hC0]
          refine ENNReal.coe_le_coe.mpr ?_
          rw [← NNReal.coe_le_coe]
          simpa [Real.norm_eq_abs] using hCH ω s
        calc (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal C ^ 2 := pow_le_pow_left' h1 2
          _ = ENNReal.ofReal (C ^ 2) := (ENNReal.ofReal_pow hC0 2).symm
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
        simp
    calc ∫⁻ s in Set.Icc (0 : ℝ) b,
          (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) b,
            (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s ∂volume :=
          lintegral_mono hptw
      _ ≤ ∫⁻ s, (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s ∂volume :=
          MeasureTheory.setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (C ^ 2) * volume (Set.Ioc a b) := by
          rw [lintegral_indicator measurableSet_Ioc, MeasureTheory.setLIntegral_const]
      _ = ENNReal.ofReal (C ^ 2 * (b - a)) := by
          rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (C ^ 2 * (b - a)) ∂P := lintegral_mono hinner
    _ = ENNReal.ofReal (C ^ 2 * (b - a)) := by simp
