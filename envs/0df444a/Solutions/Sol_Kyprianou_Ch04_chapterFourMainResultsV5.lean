-- Prove2me | solution 1 for Kyprianou.Ch04.chapterFourMainResultsV5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:26:41.512845+00:00
-- url     : https://prove2.me/submissions/d9a8ad13-7094-48c6-8394-3e9c90e72abc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_CompensationCertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_1CertificationV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_2Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_3CertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_4CertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_6Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_totalIdleTimeTrafficRegimesV2
import Theorems.Thm_Kyprianou_Ch04_boundedVariationChangeOfVariables
import Theorems.Thm_Kyprianou_Ch04_generalLevyItoFormulaV2
import Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensationCommonNullV2
import Theorems.Thm_Kyprianou_Ch04_conditionalPredictableCompensationCommonNullV2
import Theorems.Thm_Kyprianou_Ch04_compensatedJumpIntegralTrueMartingaleAdaptedV3
import Theorems.Thm_Kyprianou_Ch04_kellaWhittTrueMartingale
import Theorems.Thm_Kyprianou_Ch04_exponentialTimeReflectedInfimumTransform
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdownTransformAndDrift
import Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricConvolutionV2
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Theorems.Thm_Kyprianou_Ch04_downwardFirstPassageUndershootLaw
import Theorems.Thm_Kyprianou_Ch04_exercise_4_1_completeV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_2_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_3_complete_v3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_4_complete_v3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_completeV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_6_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_7_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_8_completeV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_9_complete
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
/-- Cumulative Chapter 4 capstone with current corrected compensation and exercise certificates. -/
theorem solution :
    certificate_4_1_v2 ∧
    certificate_4_2_v2 ∧
    certificate_4_3_v2 ∧
    certificate_4_4_v3 ∧
    certificate_4_5_v3 ∧
    (∀
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega)))
    (hPast : ∀ (t : NNReal) (B : Set (Real × Real)),
      MeasurableSet B →
      B ⊆ Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ →
      Measurable[F t] (fun omega => N.N omega B))
    (hKernelPast : ∀ t : NNReal,
      Measurable[(F t).prod inferInstance]
        (fun z : Omega × (Real × Real) =>
          if z.2.1 ∈ Set.Icc (0 : Real) (t : Real)
          then phi z.2.1 z.2.2 z.1 else 0))
    (hLocalFinite : ∀ (t : NNReal) (n : Nat) (omega : Omega),
      N.N omega (Set.Icc (0 : Real) (t : Real) ×ˢ spanningSets levyMeasure n) ≠ ⊤)
    (hFinite : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤),
    MeasureTheory.Martingale
      (fun (t : NNReal) omega =>
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          phi z.1 z.2 omega ∂(N.N omega)) -
        (∫ s in Set.Icc (0 : Real) (t : Real),
          (∫ x, phi s x omega ∂levyMeasure) ∂volume))
      F P ) ∧
    certificate_4_7_v2 ∧
    certificate_4_8_v2 ∧
    certificate_4_9_v2 ∧
    certificate_4_10_v2 ∧
    certificate_4_11_v2 ∧
    certificate_4_12_v2 ∧
    certificate_exercise_4_1_v2 ∧
    certificate_exercise_4_2 ∧
    certificate_exercise_4_3_v3 ∧
    certificate_exercise_4_4_v3 ∧
    certificate_exercise_4_5V3 ∧
    certificate_exercise_4_6 ∧
    certificate_exercise_4_7 ∧
    certificate_exercise_4_8_v2 ∧
    certificate_exercise_4_9 := by
  exact ⟨Kyprianou.Ch04.totalIdleTimeTrafficRegimesV2,
    Kyprianou.Ch04.boundedVariationChangeOfVariables,
    Kyprianou.Ch04.generalLevyItoFormulaV2,
    Kyprianou.Ch04.nonnegativePredictableJumpCompensationCommonNullV2,
    Kyprianou.Ch04.conditionalPredictableCompensationCommonNullV2,
    Kyprianou.Ch04.compensatedJumpIntegralTrueMartingaleAdaptedV3,
    Kyprianou.Ch04.kellaWhittTrueMartingale,
    Kyprianou.Ch04.exponentialTimeReflectedInfimumTransform,
    Kyprianou.Ch04.limitingDrawdownTransformAndDrift,
    Kyprianou.Ch04.stationaryWorkloadGeometricConvolutionV2,
    Kyprianou.Ch04.smallTimeDriftLimit,
    Kyprianou.Ch04.downwardFirstPassageUndershootLaw,
    Kyprianou.Ch04.exercise_4_1_completeV2,
    Kyprianou.Ch04.exercise_4_2_complete,
    Kyprianou.Ch04.exercise_4_3_complete_v3,
    Kyprianou.Ch04.exercise_4_4_complete_v3,
    Kyprianou.Ch04.exercise_4_5_completeV3,
    Kyprianou.Ch04.exercise_4_6_complete,
    Kyprianou.Ch04.exercise_4_7_complete,
    Kyprianou.Ch04.exercise_4_8_completeV2,
    Kyprianou.Ch04.exercise_4_9_complete⟩
