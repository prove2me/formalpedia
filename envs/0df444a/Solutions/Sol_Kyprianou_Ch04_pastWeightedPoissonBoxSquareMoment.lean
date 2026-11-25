-- Prove2me | solution 1 for Kyprianou.Ch04.pastWeightedPoissonBoxSquareMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:54:21.701864+00:00
-- url     : https://prove2.me/submissions/1a2595b9-5f9a-4af6-9152-d35e671f8cc7

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Theorems.Thm_Kyprianou_Ch04_pastWeightIndependentFutureCompensatedBox
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Factor the second moment of a compensated future box against a signed past weight. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (u t : NNReal) (hut : u ≤ t) (B : Set ℝ) (hB : MeasurableSet B)
    (hFin : referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (W : Ω → ℝ) (hW : StronglyMeasurable[F u] W) (hWi : Integrable W P) :
    Integrable (fun ω => W ω * (N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω)^2) P ∧
    (∫ ω, W ω * (N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω)^2 ∂P) =
      (∫ ω, W ω ∂P) * (referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B)).toReal := by
  let C := fun ω => N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω
  have hm : MeasurableSet (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) := measurableSet_Ioc.prod hB
  have hI : IndepFun W C P :=
    Kyprianou.Ch04.pastWeightIndependentFutureCompensatedBox P ν F N hFuture u t hut B hB W hW
  have hI2 : IndepFun W (fun ω => (C ω)^2) P :=
    hI.comp measurable_id (measurable_id.pow_const (2 : ℕ))
  have hC2 : Integrable (fun ω => (C ω)^2) P :=
    LevyStochCalc.Poisson.Compensated.compensated_sq_integrable N hm hFin
  refine ⟨hI2.integrable_mul hWi hC2, ?_⟩
  change (∫ ω, W ω * (C ω)^2 ∂P) = _
  rw [hI2.integral_fun_mul_eq_mul_integral hWi.aestronglyMeasurable hC2.aestronglyMeasurable]
  rw [show (∫ ω, (C ω)^2 ∂P) = (referenceIntensity ν
      (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B)).toReal from
    LevyStochCalc.Poisson.Compensated.compensated_second_moment N hm hFin]
