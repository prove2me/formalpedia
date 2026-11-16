-- Prove2me | solution 1 for Kyprianou.sumOfIndependentLevyProcesses
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:45:12.888048+00:00
-- url     : https://prove2.me/submissions/9ff6eb83-3433-4fbd-8f21-7b2194a14e01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_independentLevySum
import Theorems.Thm_Kyprianou_Ch02_tripleIndependentPairAndSum
import Theorems.Thm_Kyprianou_Ch02_tripleIndependentCharFun
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

open Kyprianou

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : ProbabilityTheory.IsLevyProcess Xgauss P)
    (hlarge : ProbabilityTheory.IsLevyProcess Xlarge P)
    (hsmall : ProbabilityTheory.IsLevyProcess Xsmall P)
    (hind : IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => Xgauss t ω + Xlarge t ω + Xsmall t ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
        charFun (P.map (Xgauss t)) ξ *
        charFun (P.map (Xlarge t)) ξ *
        charFun (P.map (Xsmall t)) ξ := by
  have hIndependent :=
    Kyprianou.Ch02.tripleIndependentPairAndSum P Xgauss Xlarge Xsmall hind
  have hGL := hIndependent.1
  have hGLS := hIndependent.2
  have hPair : ProbabilityTheory.IsLevyProcess
      (fun t w => Xgauss t w + Xlarge t w) P :=
    Kyprianou.Ch01.independentLevySum P Xgauss Xlarge hgauss hlarge hGL
  constructor
  case left =>
    have hTriplet :=
      Kyprianou.Ch01.independentLevySum P
        (fun t w => Xgauss t w + Xlarge t w)
        Xsmall hPair hsmall hGLS
    simpa only [add_assoc] using hTriplet
  case right =>
    exact Kyprianou.Ch02.tripleIndependentCharFun P Xgauss Xlarge Xsmall hind

