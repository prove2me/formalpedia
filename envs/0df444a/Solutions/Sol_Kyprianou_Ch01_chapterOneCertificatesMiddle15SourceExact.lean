-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneCertificatesMiddle15SourceExact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:12:35.947296+00:00
-- url     : https://prove2.me/submissions/766452d3-ac61-4ea4-a0df-f2aadf41dd05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
import Theorems.Thm_Kyprianou_Ch01_lampertiBranchingToCompoundPoissonPathLawWithoutMoment
import Theorems.Thm_Kyprianou_Ch01_generalFrullaniImproper
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneIntegral
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplace
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedLowerPassage
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponentStrictConvexAndRoot
import Theorems.Thm_Kyprianou_Ch01_queueExponentialMartingaleAndPassage
import Theorems.Thm_Kyprianou_Ch01_mckeanBarrierCalculusOptimality
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhase
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianLevyExponent
import Theorems.Thm_Kyprianou_Ch01_firstWeakDescendingRenewalPotential
import Theorems.Thm_Kyprianou_Ch01_riskEmbeddedRandomWalkTails
import Theorems.Thm_Kyprianou_Ch01_exponentialAscendingLadderRenewal
import Theorems.Thm_Kyprianou_Ch01_brownianPassageHalfStableLevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option maxRecDepth 4000
open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem solution :
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
    certificate_brownianPassageHalfStableLevyProcess.{u} := by
  exact ⟨
    @lampertiBranchingToCompoundPoissonPathLawWithoutMoment, @generalFrullaniImproper,
    @stableAlphaOneCosineIntegral, @stableAlphaAboveOneIntegral,
    @inverseGaussianDensityLaplace, @brownianDiscountedLowerPassage,
    @queueLaplaceExponentStrictConvexAndRoot, @queueExponentialMartingaleAndPassage,
    @mckeanBarrierCalculusOptimality, @stableAlphaOneLogPhase, @inverseGaussianLevyExponent,
    @firstWeakDescendingRenewalPotential, @riskEmbeddedRandomWalkTails,
    @exponentialAscendingLadderRenewal, @brownianPassageHalfStableLevyProcess
  ⟩
