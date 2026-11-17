-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneV4_last33_part_a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:27:10.490676+00:00
-- url     : https://prove2.me/submissions/4786b24f-ad74-4ee6-8d0b-d27dfcaf63ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
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
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
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
    Kyprianou.Ch01.certificate_firstWeakDescendingRenewalPotential.{u} := by
  exact ⟨@generalFrullaniImproper,
    @stableAlphaOneCosineIntegral,
    @stableAlphaAboveOneIntegral,
    @inverseGaussianDensityLaplace,
    @brownianDiscountedLowerPassage,
    @queueLaplaceExponentStrictConvexAndRoot,
    @queueExponentialMartingaleAndPassage,
    @mckeanBarrierCalculusOptimality,
    @stableAlphaOneLogPhase,
    @inverseGaussianLevyExponent,
    @firstWeakDescendingRenewalPotential⟩
