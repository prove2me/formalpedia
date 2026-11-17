-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneCertificatesMiddle17SourceExact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:16:40.765208+00:00
-- url     : https://prove2.me/submissions/6d4504cf-31c2-4b8d-8e0a-fef09ef24c60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
import Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesMiddle15SourceExact
import Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesStable2SourceExact
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
    certificate_brownianPassageHalfStableLevyProcess.{u} ∧
    certificate_stableLevyExponentFormAwayFromOne ∧ certificate_stableLevyExponentFormIndexOne := by
  have hm := Kyprianou.Ch01.chapterOneCertificatesMiddle15SourceExact
  have hs := Kyprianou.Ch01.chapterOneCertificatesStable2SourceExact
  rcases hm with ⟨
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15
  ⟩
  rcases hs with ⟨h16, h17⟩
  exact ⟨
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17
  ⟩
