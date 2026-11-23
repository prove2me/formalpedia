-- Prove2me | solution 1 for Kyprianou.Ch02.normalisedBrownianPathIndependentOfPRMV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:41:48.901922+00:00
-- url     : https://prove2.me/submissions/16615d0b-1219-461d-b42c-09e81ed5499d

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P) :
    ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω - B.W 0 ω)
      (fun ω => N.N ω) P := by
  have hmeas :
      Measurable (fun f : ℝ → ℝ => fun (t : ℝ) => f t - f 0) := by
    apply measurable_pi_lambda
    intro t
    exact (measurable_pi_apply t).sub (measurable_pi_apply 0)
  simpa only [Function.comp_def, id_eq] using
    (hDrivers.comp hmeas measurable_id)
