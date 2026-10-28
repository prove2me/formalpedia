-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:16.428995+00:00
-- url     : https://prove2.me/submissions/e66a0fae-c8e9-442e-913b-802caaab3ceb

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_increment_pow_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_pow_gaussianReal_zero_readable
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integrable_cross_term_readable
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_mul_increment_mul_increment_eq_zero_readable

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
/-- The odd moments of the standard real Gaussian vanish. -/
theorem LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_odd (m : ℕ) (hm : Odd m) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have h1 : ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1)
      = ∫ x : ℝ, (-x) ^ m ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hm.neg_pow] at h1
  rw [integral_neg] at h1
  linarith
section Increments
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- The moments of a Brownian increment scale with the square root of its length. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (m : ℕ) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P
      = Real.sqrt (b - a) ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [← integral_map hmeas.aemeasurable
      (f := fun x : ℝ => x ^ m) (by fun_prop),
    W.increment_gaussian ha hab]
  exact integral_pow_gaussianReal_zero_readable _ m
/-- Odd moments of a Brownian increment vanish. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow_odd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ} (hm : Odd m) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P = 0 := by
  rw [integral_increment_pow W ha hab m, integral_pow_gaussianReal_odd m hm, mul_zero]
end Increments
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
section DirectCross
/-- A coefficient measurable at the start of an interval is orthogonal to the Brownian increment
over it. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s < u) {Y : Ω → ℝ} (hY : StronglyMeasurable[ℱ s] Y) (hYm : Measurable Y) :
    ∫ ω, Y ω * (V.W u ω - V.W s ω) ∂P = 0 := by
  have h := Ito.integral_mul_increment_pow_readable V ℱ hV hs hsu hY hYm 1
  rw [Ito.integral_increment_pow_odd V hs hsu odd_one, mul_zero] at h
  simpa only [pow_one] using h
end DirectCross
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
section SimpleIntegrands
open LevyStochCalc.Brownian.Ito
variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
/-- **The cross term vanishes, when the `Wʲ` interval starts last.** -/
theorem solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  have hΔ : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (x y : ℝ), Measurable fun ω => V.W y ω - V.W x ω :=
    fun V x y => (V.measurable_eval y).sub (V.measurable_eval x)
  have hΔℱ : ∀ (k : Fin d) {x y s : ℝ}, x ≤ s → y ≤ s →
      Measurable[ℱ s] fun ω => (W.W k).W y ω - (W.W k).W x ω := fun k x y s hxs hys =>
    (((hcoord k).measurable y).mono (ℱ.mono hys) le_rfl).sub
      (((hcoord k).measurable x).mono (ℱ.mono hxs) le_rfl)
  have hξη : StronglyMeasurable[ℱ r] fun ω => ξ ω * η ω := (hξ.mono (ℱ.mono hpr)).mul hη
  have hξηb : ∀ ω, |ξ ω * η ω| ≤ |Mξ| * |Mη| := fun ω => by
    rw [abs_mul]
    exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  rcases le_or_gt q r with hqr | hrq
  · -- the `Wⁱ` increment is already known at time `r`
    have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W p ω) * η ω :=
      ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr hqr).stronglyMeasurable).mul hη
    have h := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
      ((hξm.mul (hΔ (W.W i) p q)).mul hηm)
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  · -- split the `Wⁱ` increment at `r`
    have hsplit : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
          * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
        = fun ω => (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω))
          + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) := by
      funext ω; ring
    rw [hsplit,
      integral_add (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable (W.W i) (W.W j) hp hpr hr hrv.le hξm hηm hξb hηb)
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable (W.W i) (W.W j) hr hrq.le hr hrv.le hξm hηm hξb hηb)]
    have h1 : ∫ ω, (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
        * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
      have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W r ω - (W.W i).W p ω) * η ω :=
        ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr le_rfl).stronglyMeasurable).mul hη
      have h := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
        ((hξm.mul (hΔ (W.W i) p r)).mul hηm)
      rw [← h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [h1, zero_add]
    -- both increments now start at `r`
    rcases lt_trichotomy q v with hqv | rfl | hvq
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))
            + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
                * ((W.W j).W v ω - (W.W j).W q ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable (W.W i) (W.W j) hr hrq.le hr hrq.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          * ((W.W j).W v ω - (W.W j).W q ω)) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable (W.W i) (W.W j) hr hrq.le (hr.trans hrq.le) hqv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_readable W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) (hr.trans hrq.le) hqv
          (Y := fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          (((hξ.mono (ℱ.mono (hpr.trans hrq.le))).mul
            (hΔℱ i hrq.le le_rfl).stronglyMeasurable).mul (hη.mono (ℱ.mono hrq.le)))
          ((hξm.mul (hΔ (W.W i) r q)).mul hηm), add_zero]
    · have heq : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W q ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
              * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω)) := by
        funext ω; ring
      rw [heq]
      exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_readable W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))
            + (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
                * ((W.W i).W q ω - (W.W i).W v ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable (W.W i) (W.W j) hr hrv.le hr hrv.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          * ((W.W i).W q ω - (W.W i).W v ω)) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable (W.W i) (W.W j) (hr.trans hrv.le) hvq.le hr hrv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_readable W hij hcoord hr hrv hξη (hξm.mul hηm) hξηb,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W i) (hcoord i) (hr.trans hrv.le) hvq
          (Y := fun ω => ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          (((hξ.mono (ℱ.mono (hpr.trans hrv.le))).mul (hη.mono (ℱ.mono hrv.le))).mul
            (hΔℱ j hrv.le le_rfl).stronglyMeasurable)
          ((hξm.mul hηm).mul (hΔ (W.W j) r v)), add_zero]
