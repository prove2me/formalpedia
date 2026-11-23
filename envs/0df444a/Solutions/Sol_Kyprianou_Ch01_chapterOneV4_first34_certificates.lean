-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneV4_first34_certificates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:21:23.411204+00:00
-- url     : https://prove2.me/submissions/e1c8f19c-0bd8-479d-b415-1337dfc8e7a2

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
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
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianPassageLevySubordinatorZeroBoundaryV2
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
import Theorems.Thm_Kyprianou_Ch01_lampertiBranchingToCompoundPoissonPathLawWithoutMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem solution :
    Kyprianou.Ch01.certificate_levyKhintchineLaw ∧
    Kyprianou.Ch01.certificate_levy_khintchine_process_existsTargetedV2 ∧
    Kyprianou.Ch01.certificate_compoundPoissonCharExponent.{u} ∧
    Kyprianou.Ch01.certificate_compoundPoissonInfinitelyDivisible.{u} ∧
    Kyprianou.Ch01.certificate_frullani_complex ∧
    Kyprianou.Ch01.certificate_pollaczekKhintchineRuin.{u} ∧
    Kyprianou.Ch01.certificate_ruinDeficitIntegratedTail.{u} ∧
    Kyprianou.Ch01.certificate_lundbergBound.{u} ∧
    Kyprianou.Ch01.certificate_lundbergAsymptotic.{u} ∧
    Kyprianou.Ch01.certificate_mg1IdleOverloaded.{u} ∧
    Kyprianou.Ch01.certificate_mg1IdleCriticalAndLight.{u} ∧
    Kyprianou.Ch01.certificate_mg1StationaryWorkload.{u} ∧
    Kyprianou.Ch01.certificate_mg1UnboundedLimsup.{u} ∧
    Kyprianou.Ch01.certificate_mckeanBrownianPutOptimalRightContinuous.{u} ∧
    Kyprianou.Ch01.certificate_branchingLaplaceExponential ∧
    Kyprianou.Ch01.certificate_branchingLaplaceSemigroup ∧
    Kyprianou.Ch01.certificate_gammaLevyExponent ∧
    Kyprianou.Ch01.certificate_gammaProcessStrictIncreaseAndInfiniteActivity.{u} ∧
    Kyprianou.Ch01.certificate_inverseGaussianFirstPassageLaplaceRightContinuous.{u} ∧
    Kyprianou.Ch01.certificate_inverseGaussianPassageLevySubordinatorZeroBoundaryV2.{u} ∧
    Kyprianou.Ch01.certificate_strictStableTimeScaling.{u} ∧
    Kyprianou.Ch01.certificate_branchingLaplaceEvolution ∧
    Kyprianou.Ch01.certificate_independentLevySum.{u} ∧
    Kyprianou.Ch01.certificate_lampertiForwardClockRecovery.{u} ∧
    Kyprianou.Ch01.certificate_lampertiReverseClockRecovery.{u} ∧
    Kyprianou.Ch01.certificate_characteristicExponentialMartingale.{u} ∧
    Kyprianou.Ch01.certificate_brownianFirstPassageStableHalf.{u} ∧
    Kyprianou.Ch01.certificate_lampertiCompoundPoissonToBranchingLawNonexplosive.{u} ∧
    Kyprianou.Ch01.certificate_geometricLawInfinitelyDivisible ∧
    Kyprianou.Ch01.certificate_geometricStoppedRandomWalkInfinitelyDivisible.{u} ∧
    Kyprianou.Ch01.certificate_stableGammaIntegral ∧
    Kyprianou.Ch01.certificate_randomWalkReversalLadderIdentity.{u} ∧
    Kyprianou.Ch01.certificate_mg1IdleRegulatorIdentity.{u} ∧
    Kyprianou.Ch01.certificate_lampertiBranchingToCompoundPoissonPathLawWithoutMoment.{u,v} := by
  exact ⟨ @levyKhintchineLawTargetedBridgeV2, @levy_khintchine_process_existsTargetedV2,
    @compoundPoissonCharExponent, @compoundPoissonInfinitelyDivisible, @frullani_complex,
    @pollaczekKhintchineRuin, @ruinDeficitIntegratedTail, @lundbergBound, @lundbergAsymptotic,
    @mg1IdleOverloaded, @mg1IdleCriticalAndLight, @mg1StationaryWorkload, @mg1UnboundedLimsup,
    @mckeanBrownianPutOptimalRightContinuous, @branchingLaplaceExponential,
    @branchingLaplaceSemigroup, @gammaLevyExponent,
    @gammaProcessStrictIncreaseAndInfiniteActivity,
    @inverseGaussianFirstPassageLaplaceRightContinuous,
    @inverseGaussianPassageLevySubordinatorZeroBoundaryV2, @strictStableTimeScaling,
    @branchingLaplaceEvolution, @independentLevySum, @lampertiForwardClockRecovery,
    @lampertiReverseClockRecovery, @characteristicExponentialMartingale,
    @brownianFirstPassageStableHalf, @lampertiCompoundPoissonToBranchingLawNonexplosive,
    @geometricLawInfinitelyDivisible, @geometricStoppedRandomWalkInfinitelyDivisible,
    @stableGammaIntegral, @randomWalkReversalLadderIdentity, @mg1IdleRegulatorIdentity,
    @lampertiBranchingToCompoundPoissonPathLawWithoutMoment
  ⟩
