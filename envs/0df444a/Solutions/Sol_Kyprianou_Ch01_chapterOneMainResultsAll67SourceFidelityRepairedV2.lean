-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneMainResultsAll67SourceFidelityRepairedV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:11:40.341778+00:00
-- url     : https://prove2.me/submissions/3d5595e6-320b-451f-b772-a66d05440b47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
import Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesFirst33SourceExact
import Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesMiddle17SourceExact
import Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesLast17SourceExact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option maxRecDepth 4000
open Kyprianou.Ch01
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
    certificate_mg1IdleRegulatorIdentity.{u} ∧
    certificate_lampertiBranchingToCompoundPoissonPathLawWithoutMoment.{u,v} ∧
    certificate_generalFrullaniImproper ∧ certificate_stableAlphaOneCosineIntegral ∧
    certificate_stableAlphaAboveOneIntegral ∧ certificate_inverseGaussianDensityLaplace ∧
    certificate_brownianDiscountedLowerPassage.{u} ∧
    certificate_queueLaplaceExponentStrictConvexAndRoot ∧
    certificate_queueExponentialMartingaleAndPassage.{u} ∧
    certificate_mckeanBarrierCalculusOptimality ∧ certificate_stableAlphaOneLogPhase ∧
    certificate_inverseGaussianLevyExponent ∧
    certificate_firstWeakDescendingRenewalPotential.{u} ∧
    certificate_riskEmbeddedRandomWalkTails ∧ certificate_exponentialAscendingLadderRenewal ∧
    certificate_brownianPassageHalfStableLevyProcess.{u} ∧
    certificate_stableLevyExponentFormAwayFromOne ∧ certificate_stableLevyExponentFormIndexOne ∧
    certificate_branchingOneAncestorGeneratorFromRates ∧
    certificate_levyTripletExponentSignBridgeReviewed ∧
    certificate_continuousRepresentativeForAlmostSurePaths.{u} ∧
    certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal.{u, v} ∧
    certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul.{u, v} ∧
    certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess.{u} ∧
    certificate_reuse_levy_foundations_poissonLaw_infinitelyDivisible ∧
    certificate_reuse_ProbabilityTheory_compoundPoisson_ae_isCadlag.{u} ∧
    certificate_reuse_levy_foundations_compoundPoissonMarginalInfinitelyDivisible.{u} ∧
    certificate_reuse_MarkovProcess_isBrownianReal_brownianMotion ∧
    certificate_brownianRealExponentialMartingale.{u} ∧
    certificate_brownianDiscountedUpperPassage.{u} ∧
    certificate_firstUpperPassageNaturalRightStoppingContinuousV2.{u} ∧
    certificate_stableGammaIntegralComplexExtensionV2 ∧
    certificate_inverseGaussianFullLevyTripletV2 ∧
    certificate_brownianFirstPassageStableParametersV2.{u} ∧
    certificate_mg1IdleJointLawsExercise19vV2.{u} := by
  have hFirst33 := Kyprianou.Ch01.chapterOneCertificatesFirst33SourceExact
  rcases hFirst33 with ⟨
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33
  ⟩
  have hMiddle17 := Kyprianou.Ch01.chapterOneCertificatesMiddle17SourceExact
  rcases hMiddle17 with ⟨
    h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50
  ⟩
  have hLast17 := Kyprianou.Ch01.chapterOneCertificatesLast17SourceExact
  rcases hLast17 with ⟨
    h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67
  ⟩
  exact ⟨
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53,
    h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67
  ⟩
