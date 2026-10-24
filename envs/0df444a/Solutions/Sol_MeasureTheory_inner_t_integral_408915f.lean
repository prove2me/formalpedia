-- Prove2me | solution 1 for MeasureTheory.inner_t_integral_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:48:05.650849+00:00
-- url     : https://prove2.me/submissions/856619a6-1e73-42bd-9ba0-8564860a164c

import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal
section
namespace MeasureTheory
end MeasureTheory
open MeasureTheory
variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}
/-- Inner integral evaluation: `∫⁻ t in Ioc 0 f, ofReal(t^(p-2)) = ofReal(f^(p-1)/(p-1))`. -/
private lemma MeasureTheory.lintegral_rpow_Ioc
    {f p : ℝ} (hf : 0 < f) (hp : 1 < p) :
    ∫⁻ t in Set.Ioc (0:ℝ) f, ENNReal.ofReal (t^(p-2)) =
      ENNReal.ofReal (f^(p-1)/(p-1)) := by
  have hpm1 : -1 < p - 2 := by linarith
  rw [show (f^(p-1)/(p-1) : ℝ) = ∫ t in Set.Ioc (0:ℝ) f, t^(p-2) from ?_]
  · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · apply MeasureTheory.IntegrableOn.integrable
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hf.le).mp
        (intervalIntegral.intervalIntegrable_rpow' hpm1)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ (fun t ht ↦ Real.rpow_nonneg ht.1.le _))
  rw [← intervalIntegral.integral_of_le hf.le]
  rw [integral_rpow (Or.inl hpm1)]
  have hzp : (0:ℝ)^(p - 2 + 1) = 0 := Real.zero_rpow (by linarith : p - 2 + 1 ≠ 0)
  rw [hzp, show p - 2 + 1 = p - 1 by ring]
  ring
namespace MeasureTheory
end MeasureTheory
open MeasureTheory in
/-- Pointwise inner integral: for `fstar ≥ 0`, integrating `t^(p-2)` against
    the indicator `𝟙{0 < t ≤ fstar}` evaluates to `fstar^(p-1)/(p-1)`. -/
 lemma solution
    {fstar p : ℝ} (hfstar : 0 ≤ fstar) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      = ENNReal.ofReal (fstar ^ (p - 1) / (p - 1)) := by
  rcases hfstar.lt_or_eq with hpos | hzero
  · -- fstar > 0: rewrite indicator-restricted integral as setLIntegral on Ioc.
    have h_eq : Set.EqOn
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
            {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
        ((Set.Ioc 0 fstar).indicator (fun t ↦ ENNReal.ofReal (t ^ (p - 2))))
        (Set.Ioi (0:ℝ)) := by
      intro t ht
      simp only
      by_cases hle : t ≤ fstar
      · have hmem1 : t ∈ {t : ℝ | t ≤ fstar} := hle
        have hmem2 : t ∈ Set.Ioc (0:ℝ) fstar := ⟨ht, hle⟩
        rw [Set.indicator_of_mem hmem1, mul_one, Set.indicator_of_mem hmem2]
      · have hnmem1 : t ∉ {t : ℝ | t ≤ fstar} := hle
        have hnmem2 : t ∉ Set.Ioc (0:ℝ) fstar := fun h ↦ hle h.2
        rw [Set.indicator_of_notMem hnmem1, mul_zero, Set.indicator_of_notMem hnmem2]
    rw [setLIntegral_congr_fun measurableSet_Ioi h_eq]
    have hsubset : Set.Ioc (0:ℝ) fstar ⊆ Set.Ioi 0 :=
      fun _ ht ↦ ht.1
    have : ∫⁻ t in Set.Ioi (0:ℝ), (Set.Ioc 0 fstar).indicator
              (fun t ↦ ENNReal.ofReal (t ^ (p - 2))) t
            = ∫⁻ t in Set.Ioc (0:ℝ) fstar, ENNReal.ofReal (t ^ (p - 2)) := by
      rw [setLIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_left.mpr hsubset]
    rw [this]
    exact lintegral_rpow_Ioc hpos hp
  · -- fstar = 0: both sides are 0.
    subst hzero
    have h_eq : Set.EqOn
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
            {t : ℝ | t ≤ (0:ℝ)}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
        (fun _ ↦ 0) (Set.Ioi (0:ℝ)) := by
      intro t ht
      simp only
      have hnot : t ∉ {t : ℝ | t ≤ (0:ℝ)} := by
        change ¬ t ≤ 0
        exact not_le.mpr ht
      rw [Set.indicator_of_notMem hnot, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi h_eq, lintegral_zero]
    have hp10 : p - 1 ≠ 0 := by linarith
    simp [Real.zero_rpow hp10]
