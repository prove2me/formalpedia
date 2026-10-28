-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:12.845994+00:00
-- url     : https://prove2.me/submissions/681abcbd-8c46-4f74-972e-ee31cb068440

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_eval_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_zero_eval_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_integralAgainst_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.stepIoc_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    ∀ i : Fin (stepIoc Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc Ω ha hab).partition i.castSucc)) ((stepIoc Ω ha hab).ξ i) := by
  intro i
  fin_cases i <;> exact MeasureTheory.stronglyMeasurable_const
theorem LevyStochCalc.Brownian.Ito.stepIoc₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b) :
    ∀ i : Fin (stepIoc₀ Ω hb).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc₀ Ω hb).partition i.castSucc)) ((stepIoc₀ Ω hb).ξ i) := by
  intro i
  fin_cases i
  exact MeasureTheory.stronglyMeasurable_const
theorem LevyStochCalc.Brownian.Ito.stepIoc_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) (M : ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) :
    (stepIoc Ω ha hab).integralAgainst M t ω = M (min b t) ω - M (min a t) ω := by
  have hrw : (stepIoc Ω ha hab).integralAgainst M t ω
      = ∑ i : Fin 2, (![fun _ => (0 : ℝ), fun _ => (1 : ℝ)] : Fin 2 → Ω → ℝ) i ω
        * (M (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
          - M (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_two]
  simp
theorem LevyStochCalc.Brownian.Ito.stepIoc₀_integralAgainst {b : ℝ} (hb : 0 < b) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).integralAgainst M t ω = M (min b t) ω - M (min 0 t) ω := by
  have hrw : (stepIoc₀ Ω hb).integralAgainst M t ω
      = ∑ i : Fin 1, (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω
        * (M (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
          - M (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_one]
  simp
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
/-- **Locality of the `L²` Itô integral.** Restricting the integrand to `(a, b]` gives the
increment of the integral across `(a, b]`. -/
theorem solution
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (him : Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s))
    (hip : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) him hip hiq t
      =ᵐ[P] fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min b t) ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min a t) ω := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIoc_zero_eval_readable]
    have hpt : ∀ (ω : Ω) (s : ℝ), (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s
        = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_readable W ℱ hℱ (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab)
      (LevyStochCalc.Brownian.Ito.stepIoc₀_adapt ℱ hab) H hm hp hq him' hip' hiq' ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => LevyStochCalc.Brownian.Ito.stepIoc₀_integralAgainst hab _ t ω)
  · have hfun : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIoc_eval_readable]
    have hpt : ∀ (ω : Ω) (s : ℝ), (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s
        = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_readable W ℱ hℱ (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab)
      (LevyStochCalc.Brownian.Ito.stepIoc_adapt ℱ ha' hab) H hm hp hq him' hip' hiq' ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => LevyStochCalc.Brownian.Ito.stepIoc_integralAgainst ha' hab _ t ω)
