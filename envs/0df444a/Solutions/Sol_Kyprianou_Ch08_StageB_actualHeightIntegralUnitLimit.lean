-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actualHeightIntegralUnitLimit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:56:50.200098+00:00
-- url     : https://prove2.me/submissions/6ca062a9-752a-409c-b874-22a116d7209a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightUnrestrictedUpcrossingNormalisation
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightRestrictedIntegralExhausts
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto
      (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
      Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
      atTop (nhds 1) := by
  have hnorm :=
    Kyprianou.Ch08.StageB.actualHeightUnrestrictedUpcrossingNormalisation
      P D ψ W hψ hW q hq
  have hexhaust :=
    Kyprianou.Ch08.StageB.actualHeightRestrictedIntegralExhausts
      P D ψ W hψ hW q hq
  simpa only [hnorm] using hexhaust