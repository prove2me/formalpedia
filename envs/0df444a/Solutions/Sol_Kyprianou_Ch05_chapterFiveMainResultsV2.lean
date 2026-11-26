-- Prove2me | solution 1 for Kyprianou.Ch05.chapterFiveMainResultsV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:33:55.069349+00:00
-- url     : https://prove2.me/submissions/8b534a1f-5431-4216-971e-1c5dbc1eef2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupA
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupB
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupC
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupD
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupE
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheoremV2
import Theorems.Thm_Kyprianou_Ch05_potentialRenewalIdentity
import Theorems.Thm_Kyprianou_Ch05_subordinatorPotentialRenewalLimits
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorPotentialLattice
import Theorems.Thm_Kyprianou_Ch05_renewalJointOvershootUndershoot
import Theorems.Thm_Kyprianou_Ch05_killedJointPassageKernel
import Theorems.Thm_Kyprianou_Ch05_finiteMeanPassageJointWeakLimit
import Theorems.Thm_Kyprianou_Ch05_noLandingByJumpInfiniteActivity
import Theorems.Thm_Kyprianou_Ch05_creepingEquivalenceDensity
import Theorems.Thm_Kyprianou_Ch05_creepingProbabilityBounds
import Theorems.Thm_Kyprianou_Ch05_creepingProbabilityContinuous
import Theorems.Thm_Kyprianou_Ch05_karamataTauberianInfinity
import Theorems.Thm_Kyprianou_Ch05_karamataMonotoneDensityInfinity
import Theorems.Thm_Kyprianou_Ch05_karamataTauberianZero
import Theorems.Thm_Kyprianou_Ch05_dynkinLampertiJointWeakLimit
import Theorems.Thm_Kyprianou_Ch05_regularVariationPotentialAndTailLimits
import Theorems.Thm_Kyprianou_Ch05_exercise51ProveTheorem57
import Theorems.Thm_Kyprianou_Ch05_exercise52SpectrallyPositiveRiskJointLaw
import Theorems.Thm_Kyprianou_Ch05_exercise53SizeBiasedUniformRepresentation
import Theorems.Thm_Kyprianou_Ch05_exercise54CorrelatedBivariateQuadrupleLaw
import Theorems.Thm_Kyprianou_Ch05_exercise55ExponentialPassageAllParts
import Theorems.Thm_Kyprianou_Ch05_exercise56StableSubordinatorAllParts
import Theorems.Thm_Kyprianou_Ch05_exercise57TransformsAndConverseAllParts
import Theorems.Thm_Kyprianou_Ch05_exercise58KilledTailRatioAllParts
import Theorems.Thm_Kyprianou_Ch05_exercise59ZeroDriftPolarPoints
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

/-- Complete chapter certificate requiring every numbered result and exercise. -/
theorem solution :
    (∀ (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F),
    let mu := ∫ x : Real, x ∂F;
        let V := renewalMeasure F;
        ((NonLatticeMeasure F →
          ∀ y : Real, 0 < y →
            Tendsto
              (fun x : Real => (V (Set.Ioc x (x + y))).toReal)
              atTop (nhds (y / mu))) ∧
         (NonLatticeMeasure F →
          ∀ h : Real → Real, Measurable h → DirectlyRiemannIntegrable h →
            Tendsto
              (fun x : Real =>
                ∫ z in Set.Icc (0 : Real) x, h (x - z) ∂V)
              atTop
              (nhds ((∫ z in Set.Ici (0 : Real), h z ∂volume) / mu))) ∧
         (Tendsto
           (fun x : Real => (V (Set.Icc (0 : Real) x)).toReal / x)
           atTop (nhds (1 / mu))))) ∧
    certificate_5_2 ∧
    certificate_5_3 ∧
    certificate_5_4 ∧
    certificate_5_5 ∧
    certificate_5_6 ∧
    certificate_5_7 ∧
    certificate_5_8 ∧
    certificate_5_9 ∧
    certificate_5_10 ∧
    certificate_5_11 ∧
    certificate_5_13 ∧
    certificate_5_14 ∧
    certificate_5_15 ∧
    certificate_5_16 ∧
    certificate_5_17 ∧
    certificate_exercise_5_1 ∧
    certificate_exercise_5_2 ∧
    certificate_exercise_5_3 ∧
    certificate_exercise_5_4 ∧
    certificate_exercise_5_5 ∧
    certificate_exercise_5_6 ∧
    certificate_exercise_5_7 ∧
    certificate_exercise_5_8 ∧
    certificate_exercise_5_9 := by
  exact ⟨
    Kyprianou.Ch05.classicalRenewalTheoremV2,
    Kyprianou.Ch05.potentialRenewalIdentity,
    Kyprianou.Ch05.subordinatorPotentialRenewalLimits,
    Kyprianou.Ch05.killedSubordinatorPotentialLattice,
    Kyprianou.Ch05.renewalJointOvershootUndershoot,
    Kyprianou.Ch05.killedJointPassageKernel,
    Kyprianou.Ch05.finiteMeanPassageJointWeakLimit,
    Kyprianou.Ch05.noLandingByJumpInfiniteActivity,
    Kyprianou.Ch05.creepingEquivalenceDensity,
    Kyprianou.Ch05.creepingProbabilityBounds,
    Kyprianou.Ch05.creepingProbabilityContinuous,
    Kyprianou.Ch05.karamataTauberianInfinity,
    Kyprianou.Ch05.karamataMonotoneDensityInfinity,
    Kyprianou.Ch05.karamataTauberianZero,
    Kyprianou.Ch05.dynkinLampertiJointWeakLimit,
    Kyprianou.Ch05.regularVariationPotentialAndTailLimits,
    Kyprianou.Ch05.exercise51ProveTheorem57,
    Kyprianou.Ch05.exercise52SpectrallyPositiveRiskJointLaw,
    Kyprianou.Ch05.exercise53SizeBiasedUniformRepresentation,
    Kyprianou.Ch05.exercise54CorrelatedBivariateQuadrupleLaw,
    Kyprianou.Ch05.exercise55ExponentialPassageAllParts,
    Kyprianou.Ch05.exercise56StableSubordinatorAllParts,
    Kyprianou.Ch05.exercise57TransformsAndConverseAllParts,
    Kyprianou.Ch05.exercise58KilledTailRatioAllParts,
    Kyprianou.Ch05.exercise59ZeroDriftPolarPoints
  ⟩


