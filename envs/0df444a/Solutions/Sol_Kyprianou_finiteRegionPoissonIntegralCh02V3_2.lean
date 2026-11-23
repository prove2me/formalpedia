-- Prove2me | solution 2 for Kyprianou.finiteRegionPoissonIntegralCh02V3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:08:14.402041+00:00
-- url     : https://prove2.me/submissions/a36d9d2a-e695-4bc3-8048-4c271b5a264d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralStartZeroV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralIndependentIncrementsNNRealV2
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralStationaryIncrementsNNRealV2
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralCadlagAEV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralCharFunV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

open Kyprianou
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false


theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)


 := by
  refine ⟨{
    start_zero := ?_
    indep_increments := ?_
    stationary_increments := ?_
    cadlag_ae := ?_}, ?_⟩
  · exact Kyprianou.Ch02.finiteRegionPoissonIntegralStartZeroV1
      P ν N B hB hfinite
  · exact Kyprianou.Ch02.finiteRegionPoissonIntegralIndependentIncrementsNNRealV2
      P ν N B hB hfinite
  · exact Kyprianou.Ch02.finiteRegionPoissonIntegralStationaryIncrementsNNRealV2
      P ν N B hB hfinite
  · exact Kyprianou.Ch02.finiteRegionPoissonIntegralCadlagAEV1
      P ν N B hB hfinite
  · exact Kyprianou.Ch02.finiteRegionPoissonIntegralCharFunV1
      P ν N B hB hfinite
