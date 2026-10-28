-- Prove2me | solution 1 for LevyStochCalc.abs_setIntegral_Icc_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:17.756842+00:00
-- url     : https://prove2.me/submissions/b2dbcb9d-deb5-46b2-9dfd-12f00b30b325

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement
import Theorems.Thm_LevyStochCalc_abs_setIntegral_Ioc_le_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
/-- A bounded measurable function is integrable on any set of finite measure. -/
theorem LevyStochCalc.integrableOn_of_bounded_of_measurable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn f s volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hs hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u
/-- The increment of `t ↦ ∫_{[0,t]} f` across `(a, b]` is the integral over `(a, b]`. -/
theorem LevyStochCalc.setIntegral_Icc_sub_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume
      = ∫ s in Set.Ioc a b, f s ∂volume := by
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) a) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  have hint2 : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
    add_sub_cancel_left]
/-- The integral of a bounded function over `[0, t]` is `B`-Lipschitz in `t`. -/
theorem solution {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, |f s| ≤ B) (t t' : ℝ) :
    |(∫ s in Set.Icc (0 : ℝ) t', f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume|
      ≤ B * |t' - t| := by
  have hIcc : ∀ u : ℝ, 0 ≤ u →
      (∫ s in Set.Icc (0 : ℝ) u, f s ∂volume) = ∫ s in Set.Ioc (0 : ℝ) u, f s ∂volume := by
    intro u _
    rw [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  have hempty : ∀ u : ℝ, u < 0 → (∫ s in Set.Icc (0 : ℝ) u, f s ∂volume) = 0 := by
    intro u hu
    rw [Set.Icc_eq_empty (not_le.mpr hu), MeasureTheory.setIntegral_empty]
  have key : ∀ a b : ℝ, a ≤ b →
      |(∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume|
        ≤ B * (b - a) := by
    intro a b hab
    rcases lt_or_ge b 0 with hb | hb
    · rw [hempty b hb, hempty a (lt_of_le_of_lt hab hb)]
      simpa using mul_nonneg hB0 (by linarith)
    · rcases lt_or_ge a 0 with ha | ha
      · rw [hempty a ha, sub_zero, hIcc b hb]
        refine le_trans (LevyStochCalc.abs_setIntegral_Ioc_le_readable hf hB hb) ?_
        have : (0 : ℝ) ≤ -a := by linarith
        nlinarith
      · rw [LevyStochCalc.setIntegral_Icc_sub_Icc hf hB ha hab]
        exact LevyStochCalc.abs_setIntegral_Ioc_le_readable hf hB hab
  rcases le_total t t' with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t' - t)]
    exact key t t' h
  · rw [abs_sub_comm ((∫ s in Set.Icc (0 : ℝ) t', f s ∂volume)),
      abs_sub_comm t' t, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - t')]
    exact key t' t h
