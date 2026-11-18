-- Prove2me | solution 2 for Kyprianou.Ch02.tripleIndependentPairAndSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:47:50.772206+00:00
-- url     : https://prove2.me/submissions/adb460c4-697c-44b8-accc-18aec2c311bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Theorems.Thm_Kyprianou_Ch02_tripleIndependentPairSumThird

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
      (fun ω => fun t : ℝ≥0 => Xlarge t ω) P ∧
    ProbabilityTheory.IndepFun
      (fun ω => fun t : ℝ≥0 => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t : ℝ≥0 => Xsmall t ω) P := by
  constructor
  · simpa [Kyprianou.IndependentLevyItoComponents] using
      (hind.indepFun (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide))
  · exact Kyprianou.Ch02.tripleIndependentPairSumThird
      P Xgauss Xlarge Xsmall hind
