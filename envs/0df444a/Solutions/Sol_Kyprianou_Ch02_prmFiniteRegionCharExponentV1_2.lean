-- Prove2me | solution 2 for Kyprianou.Ch02.prmFiniteRegionCharExponentV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:35:35.92892+00:00
-- url     : https://prove2.me/submissions/1acec66f-2e18-44a6-bf25-0b0a55a80b60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkCharExponentKLSV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleCharToRawKLSV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Reduce the raw marked characteristic exponent to simple marks and a limit transfer. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by
  exact Kyprianou.Ch02.prmFiniteSimpleCharToRawKLSV1
    P ν N B hB hfinite
      (Kyprianou.Ch02.prmFiniteSimpleMarkCharExponentKLSV1
        P ν N B hB hfinite)
