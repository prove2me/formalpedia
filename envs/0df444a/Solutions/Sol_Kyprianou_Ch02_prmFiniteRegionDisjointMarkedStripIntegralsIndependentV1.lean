-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionDisjointMarkedStripIntegralsIndependentV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:27:32.103579+00:00
-- url     : https://prove2.me/submissions/1071d077-7300-45cf-947f-bb8fadf54b7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStripEvalSigmaJointIndependentV1
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableLocalEvalSigmaV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      iIndepFun (fun (i : Fin n) (ω : Ω) =>
        ∫ z in (Set.Ioc (t i.castSucc : ℝ) (t i.succ : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) P := by
  intro n t ht
  have hSig :=
    Kyprianou.Ch02.prmFiniteRegionStripEvalSigmaJointIndependentV1
      P ν N B hB hfinite n t ht
  apply (iIndepFun_iff_iIndep
    (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) _ P).2
  refine iIndep_of_iIndep_of_le hSig ?_
  intro i
  exact (Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1
    P ν N (Set.Ioc (t i.castSucc : ℝ) (t i.succ : ℝ) ×ˢ B)
    (measurableSet_Ioc.prod hB)).comap_le
