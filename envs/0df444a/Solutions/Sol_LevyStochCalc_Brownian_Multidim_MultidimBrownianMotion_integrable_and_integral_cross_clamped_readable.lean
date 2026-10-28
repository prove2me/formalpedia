-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_and_integral_cross_clamped_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:24:05.103986+00:00
-- url     : https://prove2.me/submissions/49286a96-7c84-49b5-be32-272d3ff25346

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integrable_cross_term_readable
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_cross_increment_eq_zero_of_le_readable

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
/-- Clamping an interval to `(-∞, t]` either collapses it or leaves its left endpoint alone. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.min_eq_or_lt_min {p q : ℝ} (h : p < q) (t : ℝ) :
    min p t = min q t ∨ (min p t = p ∧ p < min q t) := by
  rcases lt_or_ge t q with htq | hqt
  · rcases lt_or_ge p t with hpt | htp
    · exact Or.inr ⟨min_eq_left hpt.le, by rw [min_eq_right htq.le]; exact hpt⟩
    · exact Or.inl (by rw [min_eq_right htp, min_eq_right htq.le])
  · exact Or.inr ⟨min_eq_left (h.le.trans hqt), by rw [min_eq_left hqt]; exact h⟩
/-- **The cross term vanishes.** For distinct coordinates the two increments are uncorrelated
against bounded coefficients measurable at the left endpoints, in either order. -/
theorem LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpq : p < q) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  rcases le_or_gt p r with hpr | hrp
  · exact integral_cross_increment_eq_zero_of_le_readable W hij hcoord hp hr hrv hpr hξ hξm hξb hη hηm hηb
  · have h := integral_cross_increment_eq_zero_of_le_readable W hij.symm hcoord (q := v) hr hp hpq hrp.le
      hη hηm hηb hξ hξm hξb
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
/-- A single clamped cross term is integrable and has zero mean. -/
lemma solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hpq : p < q)
    (hr : 0 ≤ r) (hrv : r < v) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ)
    (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) (t t' : ℝ) :
    Integrable (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) P
    ∧ ∫ ω, (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω)) ∂P = 0 := by
  rcases LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.min_eq_or_lt_min hpq t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
        * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
  · rcases LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.min_eq_or_lt_min hrv t' with hc' | ⟨hre, hrlt⟩
    · have hz : (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
          * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) = fun _ => (0 : ℝ) := by
        funext ω; rw [hc']; ring
      rw [hz]
      exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
    · rw [hpe, hre]
      exact ⟨LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable (W.W i) (W.W j) hp hplt.le hr hrlt.le hξm hηm hξb hηb,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero W hij hcoord hp hr hrlt hplt hξ hξm hξb hη hηm hηb⟩
