-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:17:51.784795+00:00
-- url     : https://prove2.me/submissions/7d4f1c04-312a-4362-bef3-9e97f9610e54

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Bounded time windows over finite mark sets have finite Poisson intensity. -/
theorem solution
    (ν : Measure ℝ) [SigmaFinite ν]
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (a b : ℝ≥0) :
    LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B) ≠ ⊤ := by
  have hvalue :
      LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B) =
      ENNReal.ofReal ((b : ℝ) - (a : ℝ)) * ν B := by
    rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc]
    congr 1
    have hset :
        Set.Ioc (a : ℝ) (b : ℝ) ∩ Set.Ici (0 : ℝ) =
        Set.Ioc (a : ℝ) (b : ℝ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici,
        and_iff_left_iff_imp]
      have ha : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show (0 : ℝ≥0) ≤ a from zero_le)
      exact fun h => ha.trans h.1.le
    rw [hset, Real.volume_Ioc]
  rw [hvalue]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
