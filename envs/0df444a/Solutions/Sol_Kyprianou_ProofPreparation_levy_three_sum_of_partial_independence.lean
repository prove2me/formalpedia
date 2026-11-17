-- Prove2me | solution 1 for Kyprianou.ProofPreparation.levy_three_sum_of_partial_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:35:12.15527+00:00
-- url     : https://prove2.me/submissions/a4e6c3fa-4c8b-4cf1-b69f-dd3c69a5378c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Theorems.Thm_Kyprianou_Ch01_independentLevySum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall)
    (hpairThird : IndepFun
      (fun ω => fun t => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t => Xsmall t ω) P) :
    IsLevyProcess (fun t ω =>
      Xgauss t ω + Xlarge t ω + Xsmall t ω) P := by
  have hpair : IndepFun
      (fun ω => fun t => Xgauss t ω)
      (fun ω => fun t => Xlarge t ω) P := by
    simpa [Kyprianou.IndependentLevyItoComponents] using
      (hind.indepFun (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide))
  have hsum : IsLevyProcess
      (fun t ω => Xgauss t ω + Xlarge t ω) P :=
    Kyprianou.Ch01.independentLevySum P Xgauss Xlarge hgauss hlarge hpair
  exact Kyprianou.Ch01.independentLevySum P
    (fun t ω => Xgauss t ω + Xlarge t ω) Xsmall hsum hsmall hpairThird
