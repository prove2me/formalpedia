-- Prove2me | solution 1 for Kyprianou.Ch04.pastWeightCompensatedFutureBoxCentered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:09:17.004021+00:00
-- url     : https://prove2.me/submissions/71bcf52f-76af-4a27-93ed-3ef436bd766b

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_pastWeightIndependentFutureCompensatedBox
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An integrable past weight has zero centred cross moment with a future Poisson box. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure Real) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (u t : NNReal) (hut : u ≤ t)
    (B : Set Real) (hB : MeasurableSet B)
    (hFin : referenceIntensity nu (Set.Ioc (u : Real) (t : Real) ×ˢ B) ≠ ⊤)
    (f : Omega → Real)
    (hf : @StronglyMeasurable Omega Real _ (F u) f)
    (_hfi : Integrable f P)
    (_hprod : Integrable (fun omega =>
      f omega * N.compensated (Set.Ioc (u : Real) (t : Real) ×ˢ B) omega) P) :
    (∫ omega, f omega * N.compensated (Set.Ioc (u : Real) (t : Real) ×ˢ B) omega ∂P) = 0 := by
  have hbox : MeasurableSet (Set.Ioc (u : Real) (t : Real) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hIndep : IndepFun f
      (fun omega => N.compensated (Set.Ioc (u : Real) (t : Real) ×ˢ B) omega) P :=
    Kyprianou.Ch04.pastWeightIndependentFutureCompensatedBox
      P nu F N hFuture u t hut B hB f hf
  rw [hIndep.integral_fun_mul_eq_mul_integral
    (hf.mono (F.le' u)).aestronglyMeasurable
    (((ENNReal.measurable_toReal.comp (N.measurable_eval hbox)).sub_const _).aestronglyMeasurable)]
  rw [LevyStochCalc.Poisson.Compensated.compensated_mean_zero N hbox hFin, mul_zero]
