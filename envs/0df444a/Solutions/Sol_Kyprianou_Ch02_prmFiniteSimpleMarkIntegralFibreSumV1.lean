-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteSimpleMarkIntegralFibreSumV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:57:09.699554+00:00
-- url     : https://prove2.me/submissions/4d6fa9bf-07ca-449f-8469-336722a94fa0

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_realSimpleMarkIntegralFiniteMeasureFibreSumV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (f : SimpleFunc ℝ ℝ) (ω : Ω)
    (hfin : N.N ω R < ⊤) :
    (∫ z in R, f z.2 ∂(N.N ω)) =
      ∑ x ∈ f.range,
        (N.N ω (R ∩ {z : ℝ × ℝ | f z.2 = x})).toReal * x := by
  letI : IsFiniteMeasure ((N.N ω).restrict R) :=
    ⟨by simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hfin⟩
  have hEq := Kyprianou.Ch02.realSimpleMarkIntegralFiniteMeasureFibreSumV1
    ((N.N ω).restrict R) f
  convert hEq using 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  have hfib : MeasurableSet {p : ℝ × ℝ | f p.2 = x} :=
    (f.measurableSet_fiber x).preimage measurable_snd
  rw [Measure.restrict_apply hfib, Set.inter_comm]
