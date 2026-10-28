-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:36.021521+00:00
-- url     : https://prove2.me/submissions/494f4901-3bbf-44c9-8dc1-81ac5c79b9b2

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoPullOut
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIocMul_eval_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIocMul_zero_eval_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indicator_Ioc_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_integralAgainst_readable

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

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoPullOut.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.stepIocMul_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    ∀ i : Fin (stepIocMul Ω ha hab V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul Ω ha hab V hVb hVm).partition i.castSucc))
      ((stepIocMul Ω ha hab V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  · exact MeasureTheory.stronglyMeasurable_const
  · exact hVa
theorem LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ 0) V) :
    ∀ i : Fin (stepIocMul₀ Ω hb V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul₀ Ω hb V hVb hVm).partition i.castSucc))
      ((stepIocMul₀ Ω hb V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  exact hVa
theorem LevyStochCalc.Brownian.Ito.stepIocMul_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIocMul Ω ha hab V hVb hVm).integralAgainst M t ω
      = V ω * (M (min b t) ω - M (min a t) ω) := by
  have hrw : (stepIocMul Ω ha hab V hVb hVm).integralAgainst M t ω
      = ∑ i : Fin 2, (![fun _ => (0 : ℝ), V] : Fin 2 → Ω → ℝ) i ω
        * (M (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
          - M (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_two]
  simp
theorem LevyStochCalc.Brownian.Ito.stepIocMul₀_integralAgainst {b : ℝ} (hb : 0 < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIocMul₀ Ω hb V hVb hVm).integralAgainst M t ω
      = V ω * (M (min b t) ω - M (min 0 t) ω) := by
  have hrw : (stepIocMul₀ Ω hb V hVb hVm).integralAgainst M t ω
      = ∑ i : Fin 1, (![V] : Fin 1 → Ω → ℝ) i ω
        * (M (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
          - M (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_one]
  simp
section PullOut
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ in
/-- **A past weight passes inside an Itô integral over a window.** For `V` bounded and
`ℱ_a`-measurable and an integrand restricted to `(a, b]`, multiplying by `V` outside the integral
is the same as multiplying the integrand by `V`. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (him : Measurable (Function.uncurry fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s))
    (hip : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hvm : Measurable (Function.uncurry fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s))
    (hvp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s)
    (hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    (fun ω => V ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s) him hip hiq t ω)
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s) hvm hvp hvq t := by
  have hloc := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_readable W ℱ hℱ K hm hp hq ha hab him hip hiq ht
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hpt : ∀ (ω : Ω) (s : ℝ),
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s
          = V ω * LevyStochCalc.Brownian.Ito.indIoc Ω 0 b ω s * K ω s := by
      intro ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul_zero_eval_readable]
    have hGeval : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s)
        = fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω 0 b ω s * K ω s := by
      funext ω s; exact hpt ω s
    have hmm : Measurable (Function.uncurry fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s) := by rw [hGeval]; exact hvm
    have hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s := by rw [hGeval]; exact hvp
    have hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hvq T hT
    have hass := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_readable W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm) (LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt ℱ hab hVb hVm hVa) K hm hp hq
      hmm hmp hmq ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hGeval hmm hmp hmq hvm hvp hvq t] at hass
    refine Filter.EventuallyEq.trans ?_ hass
    filter_upwards [hloc] with ω hω
    rw [LevyStochCalc.Brownian.Ito.stepIocMul₀_integralAgainst]
    exact congrArg (fun x => V ω * x) hω
  · have hpt : ∀ (ω : Ω) (s : ℝ),
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s
          = V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s := by
      intro ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul_eval_readable]
    have hGeval : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s)
        = fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s := by
      funext ω s; exact hpt ω s
    have hmm : Measurable (Function.uncurry fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s) := by rw [hGeval]; exact hvm
    have hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s := by rw [hGeval]; exact hvp
    have hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hvq T hT
    have hass := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_readable W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm) (LevyStochCalc.Brownian.Ito.stepIocMul_adapt ℱ ha' hab hVb hVm hVa) K hm hp hq
      hmm hmp hmq ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hGeval hmm hmp hmq hvm hvp hvq t] at hass
    refine Filter.EventuallyEq.trans ?_ hass
    filter_upwards [hloc] with ω hω
    rw [LevyStochCalc.Brownian.Ito.stepIocMul_integralAgainst]
    exact congrArg (fun x => V ω * x) hω
