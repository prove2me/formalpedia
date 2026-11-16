-- Prove2me | solution 1 for Kyprianou.Ch02.tripleIndependentGaussianLargePair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:50:34.472511+00:00
-- url     : https://prove2.me/submissions/ff844e16-c6cc-468d-9b7e-c6da257db2bd

import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ProbabilityTheory.IndepFun
      (fun ω => fun t : ℝ≥0 => Xgauss t ω)
      (fun ω => fun t : ℝ≥0 => Xlarge t ω) P := by
  have h01 := ProbabilityTheory.iIndepFun.indepFun
    (i := (0 : Fin 3)) (j := (1 : Fin 3)) hind (by decide)
  simpa [Kyprianou.IndependentLevyItoComponents] using h01

