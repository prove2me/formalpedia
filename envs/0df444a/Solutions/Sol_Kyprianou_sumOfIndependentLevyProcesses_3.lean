-- Prove2me | solution 3 for Kyprianou.sumOfIndependentLevyProcesses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:27:02.973132+00:00
-- url     : https://prove2.me/submissions/53fac4d4-be0d-41e9-ac1d-ab93848189f6

import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_independentLevySum
import Theorems.Thm_Kyprianou_ProofPreparation_three_levy_partial_sum_independent_of_levy
import Theorems.Thm_Kyprianou_ProofPreparation_three_levy_charfun_factorisation

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
  have hpair : IndepFun
      (fun ω => fun t => Xgauss t ω)
      (fun ω => fun t => Xlarge t ω) P := by
    simpa [Kyprianou.IndependentLevyItoComponents] using
      (hind.indepFun (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide))
  have hsum : ProbabilityTheory.IsLevyProcess
      (fun t ω => Xgauss t ω + Xlarge t ω) P :=
    Kyprianou.Ch01.independentLevySum P Xgauss Xlarge hgauss hlarge hpair
  constructor
  · exact Kyprianou.Ch01.independentLevySum P
      (fun t ω => Xgauss t ω + Xlarge t ω) Xsmall hsum hsmall
      (Kyprianou.ProofPreparation.three_levy_partial_sum_independent_of_levy
        P Xgauss Xlarge Xsmall hgauss hlarge hsmall hind)
  · intro t ξ
    exact Kyprianou.ProofPreparation.three_levy_charfun_factorisation
      P Xgauss Xlarge Xsmall hgauss hlarge hsmall hind t ξ
