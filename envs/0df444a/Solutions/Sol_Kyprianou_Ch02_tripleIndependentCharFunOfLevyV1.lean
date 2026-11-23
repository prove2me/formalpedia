-- Prove2me | solution 1 for Kyprianou.Ch02.tripleIndependentCharFunOfLevyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:43:09.435024+00:00
-- url     : https://prove2.me/submissions/518c0dbd-2fe2-4a0b-b7b0-7c80d6474ebc

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Theorems.Thm_Kyprianou_ProofPreparation_three_levy_charfun_factorisation
open Kyprianou
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : ProbabilityTheory.IsLevyProcess Xgauss P)
    (hlarge : ProbabilityTheory.IsLevyProcess Xlarge P)
    (hsmall : ProbabilityTheory.IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
        charFun (P.map (Xgauss t)) ξ *
        charFun (P.map (Xlarge t)) ξ *
        charFun (P.map (Xsmall t)) ξ  := by
  intro t ξ
  exact Kyprianou.ProofPreparation.three_levy_charfun_factorisation
    P Xgauss Xlarge Xsmall hgauss hlarge hsmall hind t ξ
