-- Prove2me | solution 1 for Kyprianou.Ch04.pastMarkedIntegralMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:21:00.881179+00:00
-- url     : https://prove2.me/submissions/50e7a6dc-3878-4e17-b5da-64d15130f5c8

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableLocalEvalSigmaV1
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Mark integrals over measurable past regions are measurable in the past filtration. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (T : NNReal) (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (hPast : ∀ C : Set (ℝ × ℝ), C ⊆ D → MeasurableSet C →
      Measurable[F T] (fun ω => N.N ω C)) :
    Measurable[F T] (fun ω => ∫ z in D, z.2 ∂(N.N ω)) := by
  apply (Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1 P ν N D hD).mono
  · refine iSup_le fun C => iSup_le fun hC => ?_
    exact measurable_iff_comap_le.mp (hPast C hC.1 hC.2)
  · exact le_rfl
