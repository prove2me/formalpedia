-- Prove2me | solution 1 for Kyprianou.Ch04.independentWeightedPoissonCellIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:28:14.092026+00:00
-- url     : https://prove2.me/submissions/b1e4600e-0701-40f3-bf5e-c0064c8c0c3a

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Theorems.Thm_Kyprianou_Ch04_independentWeightedCompensatedCellL2



open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Combine the established cell moment with the independent-weight transfer. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P ν)
    {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hFin : referenceIntensity ν B ≠ ⊤)
    (H : Ω → ℝ) (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (hIndep : IndepFun H (fun ω => N.N ω B) P) :
    Integrable (fun ω => (H ω * N.compensated B ω) ^ 2) P ∧
      (∫ ω, (H ω * N.compensated B ω) ^ 2 ∂P) =
        (referenceIntensity ν B).toReal *
          ∫ ω, H ω ^ 2 ∂P := by
  exact Kyprianou.Ch04.independentWeightedCompensatedCellL2 P ν N hB hFin H hH2
    (LevyStochCalc.Poisson.Compensated.compensated_sq_integrable N hB hFin)
    (LevyStochCalc.Poisson.Compensated.compensated_second_moment N hB hFin)
    hIndep
