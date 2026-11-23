-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPoissonIntegralStartZeroV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:04:47.111102+00:00
-- url     : https://prove2.me/submissions/1d41fdb8-973d-4896-b21e-75527b9d7b40

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false


theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (0 : ℝ) ×ˢ B), z.2 ∂(N.N ω)) =
      (fun _ : Ω => (0 : ℝ)) := by
  funext ω
  simp
