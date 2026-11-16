-- Prove2me | solution 1 for Kyprianou.Ch02.tripleIndependentPairAndSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:47:07.86726+00:00
-- url     : https://prove2.me/submissions/50864933-fe34-473d-9bc4-7d1a147965e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_tripleIndependentPairSumThird
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

open Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ProbabilityTheory.IndepFun
      (fun ω => fun t : ℝ≥0 => Xgauss t ω)
      (fun ω => fun t : ℝ≥0 => Xlarge t ω) P ∧
    ProbabilityTheory.IndepFun
      (fun ω => fun t : ℝ≥0 => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t : ℝ≥0 => Xsmall t ω) P := by
  constructor
  case left =>
    have h01 := ProbabilityTheory.iIndepFun.indepFun
      (i := (0 : Fin 3)) (j := (1 : Fin 3)) hind (by decide)
    simpa [Kyprianou.IndependentLevyItoComponents] using h01
  case right =>
    exact Kyprianou.Ch02.tripleIndependentPairSumThird P Xgauss Xlarge Xsmall hind

