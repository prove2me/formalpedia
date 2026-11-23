-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPoissonWindowCountLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:02:07.539498+00:00
-- url     : https://prove2.me/submissions/d0e43dd3-dbde-4c1a-bb22-b9d50809d871

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false


open LevyStochCalc.Poisson
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) (t : ℝ≥0) :
    P.map (fun ω => N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)) =
      LevyStochCalc.Poisson.poissonMeasureENN
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toNNReal := by
  have hrate :
      referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) =
        ENNReal.ofReal (t : ℝ) * ν B := by
    rw [referenceIntensity, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc]
    congr 1
    have hset :
        Set.Ioc (0 : ℝ) (t : ℝ) ∩ Set.Ici (0 : ℝ) =
          Set.Ioc (0 : ℝ) (t : ℝ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici,
        and_iff_left_iff_imp]
      exact fun h => h.1.le
    rw [hset, Real.volume_Ioc, sub_zero]
  apply N.poisson_law (measurableSet_Ioc.prod hB)
  rw [hrate]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
