-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:34.692993+00:00
-- url     : https://prove2.me/submissions/e84e5c64-5b96-404d-82f5-2fde88c17857

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_zero_eval_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indicator_Ioc_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.stepIoc₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b) :
    ∀ i : Fin (stepIoc₀ Ω hb).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc₀ Ω hb).partition i.castSucc)) ((stepIoc₀ Ω hb).ξ i) := by
  intro i
  fin_cases i
  exact MeasureTheory.stronglyMeasurable_const
/-- The `L²` Itô integral depends on the integrand only through the function itself. -/
theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {F₁ F₂ : Ω → ℝ → ℝ} (hEq : F₁ = F₂)
    (hm₁ : Measurable (Function.uncurry F₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ F₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry F₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ F₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ F₁ hm₁ hp₁ hq₁ t
      = stochasticIntegralBrownian W ℱ hℱ F₂ hm₂ hp₂ hq₂ t := by
  subst hEq; rfl
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Indicator
theorem LevyStochCalc.Brownian.Ito.indIoc_le_one (a b : ℝ) (ω : Ω) (s : ℝ) : |indIoc Ω a b ω s| ≤ 1 := by
  unfold indIoc
  by_cases h : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num
theorem LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc (a b : ℝ) :
    Measurable (Function.uncurry (indIoc Ω a b)) :=
  ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)
theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc₀ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ}
    (hb : 0 < b) : Probability.ProgressivelyMeasurable ℱ (indIoc Ω 0 b) := by
  have hfun : indIoc Ω 0 b = fun ω s => (stepIoc₀ Ω hb).eval s ω := by
    funext ω s; rw [stepIoc_zero_eval_readable]; rfl
  rw [hfun]
  exact (stepIoc₀ Ω hb).progressivelyMeasurable_eval ℱ (stepIoc₀_adapt ℱ hb)
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
end Indicator
end
end

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
/-- **The Itô integral to a positive time sees the integrand only at positive times.** -/
theorem solution
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t := by
  classical
  have hle1 : ∀ (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ),
      |(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| := by
    intro H ω s
    rw [abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    simpa [LevyStochCalc.Brownian.Ito.indIoc] using LevyStochCalc.Brownian.Ito.indIoc_le_one (Ω := Ω) 0 t ω s
  have hmI : ∀ {H : Ω → ℝ → ℝ}, Measurable (Function.uncurry H) →
      Measurable (Function.uncurry fun ω s =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    fun hm => (LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc (Ω := Ω) 0 t).mul hm
  have hpI : ∀ {H : Ω → ℝ → ℝ}, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H →
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (fun ω s =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    fun hp => (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc₀ ℱ ht).mul hp
  have hqI : ∀ {H : Ω → ℝ → ℝ}, (∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) →
      ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun {H} hq => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (hle1 H) hq
  have key : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
      (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s)
          (hmI hm) (hpI hp) (hqI hq) t
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
    intro H hm hp hq
    have hsplit := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_readable W ℱ hℱ H hm hp hq
      (le_refl (0 : ℝ)) ht (hmI hm) (hpI hp) (hqI hq) ht
    have hz := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H hm hp hq (le_refl (0 : ℝ))
    filter_upwards [hsplit, hz] with ω hω hω0
    rw [hω, min_self, min_eq_left ht.le]
    simpa using hω0
  have hfun : (fun (ω : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H₁ ω s)
      = fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H₂ ω s := by
    funext ω s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
    · rw [hagree ω s hs.1]
    · rw [Set.indicator_of_notMem hs, zero_mul, zero_mul]
  have hcongr := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun
    (hmI hm₁) (hpI hp₁) (hqI hq₁) (hmI hm₂) (hpI hp₂) (hqI hq₂) t
  refine ((key H₁ hm₁ hp₁ hq₁).symm.trans ?_).trans (key H₂ hm₂ hp₂ hq₂)
  rw [hcongr]
