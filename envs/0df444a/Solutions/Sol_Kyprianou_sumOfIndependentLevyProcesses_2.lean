-- Prove2me | solution 2 for Kyprianou.sumOfIndependentLevyProcesses
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:01:08.301305+00:00
-- url     : https://prove2.me/submissions/a7aef331-84aa-4172-9497-a0d5f8697456
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Theorems.Thm_Kyprianou_ProofPreparation_three_levy_partial_sum_independent
import Theorems.Thm_Kyprianou_ProofPreparation_levy_three_sum_of_partial_independence
import Theorems.Thm_Kyprianou_ProofPreparation_three_levy_charfun_factorisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false

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
        charFun (P.map (Xsmall t)) ξ
      := by
  constructor
  · exact Kyprianou.ProofPreparation.levy_three_sum_of_partial_independence
      P Xgauss Xlarge Xsmall hgauss hlarge hsmall hind
      (Kyprianou.ProofPreparation.three_levy_partial_sum_independent
        P Xgauss Xlarge Xsmall hind)
  · intro t ξ
    exact Kyprianou.ProofPreparation.three_levy_charfun_factorisation
      P Xgauss Xlarge Xsmall hgauss hlarge hsmall hind t ξ
