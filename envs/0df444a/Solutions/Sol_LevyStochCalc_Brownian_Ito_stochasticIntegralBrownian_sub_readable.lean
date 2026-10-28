-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:02.750471+00:00
-- url     : https://prove2.me/submissions/479fe906-b294-45f7-8033-c7935a6e3bb6

import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoZero
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFinsetSum
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_add_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_neg_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/Progressive.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
section
variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}
section Add
variable [NormedAddCommGroup E] {ℱ : MeasureTheory.Filtration ℝ mΩ}
/-- The pointwise difference of two progressively measurable processes is progressively
measurable. -/
theorem LevyStochCalc.Probability.ProgressivelyMeasurable.sub {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s - B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s - B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 - (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, sub_zero]
  rw [key]
  exact (hA t).sub (hB t)
end Add
end
end

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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoZero.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
/-- A constant process is progressively measurable for any filtration. -/
theorem LevyStochCalc.Probability.progressivelyMeasurable_const {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] (ℱ : Filtration ℝ mΩ) (c : E) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => c) := fun _ =>
  stronglyMeasurable_const.indicator
    (measurableSet_preimage measurable_snd measurableSet_Iic)
/-- The zero process is progressively measurable for any filtration. -/
theorem LevyStochCalc.Probability.progressivelyMeasurable_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] (ℱ : Filtration ℝ mΩ) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => (0 : E)) :=
  Probability.progressivelyMeasurable_const ℱ 0
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFinsetSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- The square-integrability of an integrand transfers along an equality of integrands. -/
theorem LevyStochCalc.Brownian.Ito.energy_lt_top_congr {F₁ F₂ : Ω → ℝ → ℝ} (h : F₁ = F₂)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  subst h
  exact hq
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- **The Itô integral is additive in its integrand, in the subtractive form.** -/
theorem solution {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hms : Measurable (Function.uncurry fun ω s => H₁ ω s - H₂ ω s))
    (hps : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s - H₂ ω s)
    (hqs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s - H₂ ω s) hms hps hqs T
      =ᵐ[P] fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω := by
  have hnegfun : (fun (ω : Ω) (s : ℝ) => -H₂ ω s) = fun ω s => (0 : ℝ) - H₂ ω s := by
    funext ω s
    ring
  have hmn : Measurable (Function.uncurry fun ω s => -H₂ ω s) := hm₂.neg
  have hpn : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => -H₂ ω s := by
    have hz : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
      LevyStochCalc.Probability.progressivelyMeasurable_zero ℱ
    exact hnegfun ▸ hz.sub hp₂
  have hqn : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T' hT'
    have hcongr : ∀ (ω : Ω) (s : ℝ), (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 = (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω s
      simp
    calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          lintegral_congr fun ω => lintegral_congr fun s => hcongr ω s
      _ < ⊤ := hq₂ T' hT'
  have hsubfun : (fun (ω : Ω) (s : ℝ) => H₁ ω s - H₂ ω s)
      = fun ω s => H₁ ω s + -H₂ ω s := by
    funext ω s
    ring
  have hma : Measurable (Function.uncurry fun ω s => H₁ ω s + -H₂ ω s) := hsubfun ▸ hms
  have hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + -H₂ ω s := hsubfun ▸ hps
  have hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s + -H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := LevyStochCalc.Brownian.Ito.energy_lt_top_congr hsubfun hqs
  rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hsubfun hms hps hqs hma hpa hqa T]
  filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add_readable W ℱ hℱ hm₁ hmn hp₁ hpn hq₁ hqn hma hpa hqa hT,
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg_readable W ℱ hℱ hm₂ hp₂ hq₂ hmn hpn hqn hT] with ω hadd hneg
  rw [hadd, hneg]
  ring
