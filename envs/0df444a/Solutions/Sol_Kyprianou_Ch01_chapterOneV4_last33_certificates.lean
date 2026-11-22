-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneV4_last33_certificates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:27:53.803134+00:00
-- url     : https://prove2.me/submissions/2de8c882-6ccc-4e4a-99ae-c927d31abe66

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
import Theorems.Thm_Kyprianou_Ch01_chapterOneV4_last33_part_a
import Theorems.Thm_Kyprianou_Ch01_chapterOneV4_last33_part_b
import Theorems.Thm_Kyprianou_Ch01_chapterOneV4_last33_part_c
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
universe u v

theorem solution :
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
  have ha := @Kyprianou.Ch01.chapterOneV4_last33_part_a
  have hb := @Kyprianou.Ch01.chapterOneV4_last33_part_b
  have hc := @Kyprianou.Ch01.chapterOneV4_last33_part_c
  simpa only [and_assoc] using And.intro ha (And.intro hb hc)
