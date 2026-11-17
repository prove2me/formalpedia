-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneCertificatesFirst33SourceExact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:06:28.004081+00:00
-- url     : https://prove2.me/submissions/ad499743-76b7-4168-a253-8efede14599a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
import Theorems.Thm_Kyprianou_Ch01_levyKhintchineLawTargetedBridgeV2
import Theorems.Thm_Kyprianou_Ch01_levy_khintchine_process_existsTargetedV2
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonCharExponent
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonInfinitelyDivisible
import Theorems.Thm_Kyprianou_Ch01_frullani_complex
import Theorems.Thm_Kyprianou_Ch01_pollaczekKhintchineRuin
import Theorems.Thm_Kyprianou_Ch01_ruinDeficitIntegratedTail
import Theorems.Thm_Kyprianou_Ch01_lundbergBound
import Theorems.Thm_Kyprianou_Ch01_lundbergAsymptotic
import Theorems.Thm_Kyprianou_Ch01_mg1IdleOverloaded
import Theorems.Thm_Kyprianou_Ch01_mg1IdleCriticalAndLight
import Theorems.Thm_Kyprianou_Ch01_mg1StationaryWorkload
import Theorems.Thm_Kyprianou_Ch01_mg1UnboundedLimsup
import Theorems.Thm_Kyprianou_Ch01_mckeanBrownianPutOptimalRightContinuous
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceExponential
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceSemigroup
import Theorems.Thm_Kyprianou_Ch01_gammaLevyExponent
import Theorems.Thm_Kyprianou_Ch01_gammaProcessStrictIncreaseAndInfiniteActivity
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageLaplaceRightContinuous
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianPassageLevySubordinator
import Theorems.Thm_Kyprianou_Ch01_strictStableTimeScaling
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceEvolution
import Theorems.Thm_Kyprianou_Ch01_independentLevySum
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardClockRecovery
import Theorems.Thm_Kyprianou_Ch01_lampertiReverseClockRecovery
import Theorems.Thm_Kyprianou_Ch01_characteristicExponentialMartingale
import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageStableHalf
import Theorems.Thm_Kyprianou_Ch01_lampertiCompoundPoissonToBranchingLawNonexplosive
import Theorems.Thm_Kyprianou_Ch01_geometricLawInfinitelyDivisible
import Theorems.Thm_Kyprianou_Ch01_geometricStoppedRandomWalkInfinitelyDivisible
import Theorems.Thm_Kyprianou_Ch01_stableGammaIntegral
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversalLadderIdentity
import Theorems.Thm_Kyprianou_Ch01_mg1IdleRegulatorIdentity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
set_option maxRecDepth 4000
set_option autoImplicit false
universe u v

theorem solution :
    certificate_levyKhintchineLaw ∧ certificate_levy_khintchine_process_existsTargetedV2 ∧
    certificate_compoundPoissonCharExponent.{u} ∧
    certificate_compoundPoissonInfinitelyDivisible.{u} ∧ certificate_frullani_complex ∧
    certificate_pollaczekKhintchineRuin.{u} ∧ certificate_ruinDeficitIntegratedTail.{u} ∧
    certificate_lundbergBound.{u} ∧ certificate_lundbergAsymptotic.{u} ∧
    certificate_mg1IdleOverloaded.{u} ∧ certificate_mg1IdleCriticalAndLight.{u} ∧
    certificate_mg1StationaryWorkload.{u} ∧ certificate_mg1UnboundedLimsup.{u} ∧
    certificate_mckeanBrownianPutOptimalRightContinuous.{u} ∧
    certificate_branchingLaplaceExponential ∧ certificate_branchingLaplaceSemigroup ∧
    certificate_gammaLevyExponent ∧
    certificate_gammaProcessStrictIncreaseAndInfiniteActivity.{u} ∧
    certificate_inverseGaussianFirstPassageLaplaceRightContinuous.{u} ∧
    certificate_inverseGaussianPassageLevySubordinator.{u} ∧
    certificate_strictStableTimeScaling.{u} ∧ certificate_branchingLaplaceEvolution ∧
    certificate_independentLevySum.{u} ∧ certificate_lampertiForwardClockRecovery.{u} ∧
    certificate_lampertiReverseClockRecovery.{u} ∧
    certificate_characteristicExponentialMartingale.{u} ∧
    certificate_brownianFirstPassageStableHalf.{u} ∧
    certificate_lampertiCompoundPoissonToBranchingLawNonexplosive.{u} ∧
    certificate_geometricLawInfinitelyDivisible ∧
    certificate_geometricStoppedRandomWalkInfinitelyDivisible.{u} ∧
    certificate_stableGammaIntegral ∧ certificate_randomWalkReversalLadderIdentity.{u} ∧
    certificate_mg1IdleRegulatorIdentity.{u} := by
  exact ⟨
    @levyKhintchineLawTargetedBridgeV2, @levy_khintchine_process_existsTargetedV2,
    @compoundPoissonCharExponent, @compoundPoissonInfinitelyDivisible, @frullani_complex,
    @pollaczekKhintchineRuin, @ruinDeficitIntegratedTail, @lundbergBound,
    @lundbergAsymptotic, @mg1IdleOverloaded, @mg1IdleCriticalAndLight,
    @mg1StationaryWorkload, @mg1UnboundedLimsup, @mckeanBrownianPutOptimalRightContinuous,
    @branchingLaplaceExponential, @branchingLaplaceSemigroup, @gammaLevyExponent,
    @gammaProcessStrictIncreaseAndInfiniteActivity,
    @inverseGaussianFirstPassageLaplaceRightContinuous,
    @inverseGaussianPassageLevySubordinator, @strictStableTimeScaling,
    @branchingLaplaceEvolution, @independentLevySum, @lampertiForwardClockRecovery,
    @lampertiReverseClockRecovery, @characteristicExponentialMartingale,
    @brownianFirstPassageStableHalf, @lampertiCompoundPoissonToBranchingLawNonexplosive,
    @geometricLawInfinitelyDivisible, @geometricStoppedRandomWalkInfinitelyDivisible,
    @stableGammaIntegral, @randomWalkReversalLadderIdentity, @mg1IdleRegulatorIdentity
  ⟩
