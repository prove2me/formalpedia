-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.compensator_sub_bounds_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:24.977467+00:00
-- url     : https://prove2.me/submissions/05433aab-9648-42a9-bf0d-e5bb30ebc4ec

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Bounds
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hm hC0 hCH in
/-- The square of a bounded integrand is integrable on every set of finite measure. -/
theorem LevyStochCalc.Brownian.Ito.integrableOn_sq (ω : Ω) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) s volume := by
  have hmeas : Measurable fun u => (H ω u) ^ 2 :=
    ((Measurable.of_uncurry_left hm).pow_const 2)
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := C ^ 2) hs
    hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (H ω u) ^ 2)]
  nlinarith [hCH ω u, abs_nonneg (H ω u), sq_abs (H ω u)]
include hm hC0 hCH in
/-- The compensator increment across `(a, b]` is between `0` and `C²(b − a)`. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω) :
    0 ≤ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume
      ∧ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume ≤ C ^ 2 * (b - a) := by
  have hmeas : Measurable fun u => (H ω u) ^ 2 :=
    ((Measurable.of_uncurry_left hm).pow_const 2)
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) (Set.Icc (0 : ℝ) a) volume :=
    LevyStochCalc.Brownian.Ito.integrableOn_sq H hm hC0 hCH ω (by simp)
  have hint2 : MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) (Set.Ioc a b) volume :=
    LevyStochCalc.Brownian.Ito.integrableOn_sq H hm hC0 hCH ω (by simp)
  have hadd : (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      = (∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
        + ∫ u in Set.Ioc a b, (H ω u) ^ 2 ∂volume := by
    rw [hsplit]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2
  rw [hadd, add_sub_cancel_left]
  refine ⟨MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun u _ => by positivity, ?_⟩
  have hle : ∫ u in Set.Ioc a b, (H ω u) ^ 2 ∂volume
      ≤ ∫ _u in Set.Ioc a b, C ^ 2 ∂volume := by
    refine MeasureTheory.setIntegral_mono_on hint2
      (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
      fun u _ => ?_
    nlinarith [hCH ω u, abs_nonneg (H ω u), sq_abs (H ω u)]
  refine hle.trans ?_
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  exact le_of_eq (mul_comm _ _)
