-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedFiniteRegionL2GivenSecondMomentV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:56:20.9688+00:00
-- url     : https://prove2.me/submissions/4055d228-f77a-43c5-bfb8-f7c83c01e315
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionRawMarkedIntegralL2V1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
    ∀ t : ℝ≥0, MemLp
      (fun ω =>
        (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) -
        (t : ℝ) * (∫ x in B, x ∂ν)) 2 P := by
  intro t
  have hraw : MemLp
      (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) 2 P :=
    Kyprianou.Ch02.prmFiniteRegionRawMarkedIntegralL2V1
      P ν N B hB hfinite hsecond t
  exact hraw.sub (memLp_const ((t : ℝ) * (∫ x in B, x ∂ν)))
