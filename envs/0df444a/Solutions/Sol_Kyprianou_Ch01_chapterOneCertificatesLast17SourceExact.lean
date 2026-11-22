-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneCertificatesLast17SourceExact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:10:57.135046+00:00
-- url     : https://prove2.me/submissions/56203d43-55d4-4dc1-a19d-6563bc8ea6f8

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorGeneratorFromRates
import Theorems.Thm_Kyprianou_Ch01_levyTripletExponentSignBridgeTargetedV2
import Theorems.Thm_Kyprianou_Ch01_continuousRepresentativeForAlmostSurePaths
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul
import Theorems.Thm_ProbabilityTheory_IsPoissonProcess_isLevyProcess
import Theorems.Thm_levy_foundations_poissonLaw_infinitelyDivisible
import Theorems.Thm_ProbabilityTheory_compoundPoisson_ae_isCadlag
import Theorems.Thm_levy_foundations_compoundPoissonMarginalInfinitelyDivisible
import Theorems.Thm_MarkovProcess_isBrownianReal_brownianMotion
import Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialMartingale
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageNaturalRightStoppingContinuousV2
import Theorems.Thm_Kyprianou_Ch01_stableGammaIntegralComplexExtensionV2
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFullLevyTripletV2
import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageStableParametersV2
import Theorems.Thm_Kyprianou_Ch01_mg1IdleJointLawsExercise19vV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option maxRecDepth 4000
open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem solution :
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
  exact ⟨
    @branchingOneAncestorGeneratorFromRates, @levyTripletExponentSignBridgeTargetedV2,
    @continuousRepresentativeForAlmostSurePaths,
    @ProbabilityTheory.IsLevyProcess.isInfinitelyDivisible_marginal,
    @ProbabilityTheory.IsLevyProcess.charFun_eq_exp_mul,
    @ProbabilityTheory.IsPoissonProcess.isLevyProcess,
    @levy_foundations_poissonLaw_infinitelyDivisible,
    @ProbabilityTheory.compoundPoisson_ae_isCadlag,
    @levy_foundations_compoundPoissonMarginalInfinitelyDivisible,
    @MarkovProcess.isBrownianReal_brownianMotion, @brownianRealExponentialMartingale,
    @brownianDiscountedUpperPassage, @firstUpperPassageNaturalRightStoppingContinuousV2,
    @stableGammaIntegralComplexExtensionV2, @inverseGaussianFullLevyTripletV2,
    @brownianFirstPassageStableParametersV2, @mg1IdleJointLawsExercise19vV2
  ⟩
