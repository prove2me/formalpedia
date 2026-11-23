-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionIndependentIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:15:06.127739+00:00
-- url     : https://prove2.me/submissions/f800e431-8979-4f46-813d-1a5df6408e2f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionDisjointMarkedStripIntegralsIndependentV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionIntegralIncrementStripAEV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P := by
  intro n t ht
  have hind :=
    Kyprianou.Ch02.prmFiniteRegionDisjointMarkedStripIntegralsIndependentV1
      P ν N B hB hfinite n t ht
  have hAE :=
    Kyprianou.Ch02.prmFiniteRegionIntegralIncrementStripAEV1
      P ν N B hB hfinite
  change iIndepFun (fun (i : Fin n) (ω : Ω) =>
    ProbabilityTheory.increment
      (fun (u : ℝ≥0) (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ B), z.2 ∂(N.N ω))
      (t i.castSucc) (t i.succ) ω) P
  apply hind.congr
  intro i
  filter_upwards [hAE] with ω hω
  have hlt : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  exact (hω (t i.castSucc) (t i.succ) hlt).symm
