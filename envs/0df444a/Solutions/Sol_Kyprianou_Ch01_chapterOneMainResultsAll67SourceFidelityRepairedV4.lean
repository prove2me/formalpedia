-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneMainResultsAll67SourceFidelityRepairedV4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:12:59.7746+00:00
-- url     : https://prove2.me/submissions/10502399-8917-4bc1-9d93-39c593e23540
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
import Theorems.Thm_Kyprianou_Ch01_chapterOneV4_first34_certificates
import Theorems.Thm_Kyprianou_Ch01_chapterOneV4_last33_certificates
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    Kyprianou.Ch01.certificate_lampertiBranchingToCompoundPoissonPathLawWithoutMoment.{u,v} ∧
    Kyprianou.Ch01.certificate_generalFrullaniImproper ∧
    Kyprianou.Ch01.certificate_stableAlphaOneCosineIntegral ∧
    Kyprianou.Ch01.certificate_stableAlphaAboveOneIntegral ∧
    Kyprianou.Ch01.certificate_inverseGaussianDensityLaplace ∧
    Kyprianou.Ch01.certificate_brownianDiscountedLowerPassage.{u} ∧
    Kyprianou.Ch01.certificate_queueLaplaceExponentStrictConvexAndRoot ∧
    Kyprianou.Ch01.certificate_queueExponentialMartingaleAndPassage.{u} ∧
    Kyprianou.Ch01.certificate_mckeanBarrierCalculusOptimality ∧
    Kyprianou.Ch01.certificate_stableAlphaOneLogPhase ∧
    Kyprianou.Ch01.certificate_inverseGaussianLevyExponent ∧
    Kyprianou.Ch01.certificate_firstWeakDescendingRenewalPotential.{u} ∧
    Kyprianou.Ch01.certificate_riskEmbeddedRandomWalkTails ∧
    Kyprianou.Ch01.certificate_exponentialAscendingLadderRenewal ∧
    Kyprianou.Ch01.certificate_brownianPassageHalfStableLevyProcessZeroBoundaryV2.{u} ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormAwayFromOne ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormIndexOne ∧
    Kyprianou.Ch01.certificate_branchingOneAncestorGeneratorFromRates ∧
    Kyprianou.Ch01.certificate_levyTripletExponentSignBridgeReviewed ∧
    Kyprianou.Ch01.certificate_continuousRepresentativeForAlmostSurePaths.{u} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess.{u} ∧
    Kyprianou.Ch01.certificate_reuse_levy_foundations_poissonLaw_infinitelyDivisible ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_compoundPoisson_ae_isCadlag.{u} ∧
    Kyprianou.Ch01.certificate_reuse_levy_foundations_compoundPoissonMarginalInfinitelyDivisible.{u} ∧
    Kyprianou.Ch01.certificate_reuse_MarkovProcess_isBrownianReal_brownianMotion ∧
    Kyprianou.Ch01.certificate_brownianRealExponentialMartingale.{u} ∧
    Kyprianou.Ch01.certificate_brownianDiscountedUpperPassage.{u} ∧
    Kyprianou.Ch01.certificate_firstUpperPassageNaturalRightStoppingContinuousV2.{u} ∧
    Kyprianou.Ch01.certificate_stableGammaIntegralComplexExtensionV2 ∧
    Kyprianou.Ch01.certificate_inverseGaussianFullLevyTripletV2 ∧
    Kyprianou.Ch01.certificate_brownianFirstPassageStableParametersV2.{u} ∧
    Kyprianou.Ch01.certificate_mg1IdleJointLawsExercise19vV2.{u} := by
  have hfirst := @Kyprianou.Ch01.chapterOneV4_first34_certificates
  have hlast := @Kyprianou.Ch01.chapterOneV4_last33_certificates
  simpa only [and_assoc] using And.intro hfirst hlast
