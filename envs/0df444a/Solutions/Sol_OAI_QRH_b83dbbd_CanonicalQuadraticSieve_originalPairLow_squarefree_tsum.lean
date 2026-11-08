-- Prove2me | solution 1 for OAI.QRH_b83dbbd.CanonicalQuadraticSieve.originalPairLow_squarefree_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:37:38.689346+00:00
-- url     : https://prove2.me/submissions/a9d23b7a-2cc4-4aa3-a983-d25ddc809d8c

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ConjugateProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedNormWeights
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_supported
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_quadraticRow_primary_squarefree
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_quadraticRow_star
import Theorems.Thm_OAI_CanonicalQuadraticSieve_originalPairLow_summable
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (I J : Ideal OAI.CanonicalQuadraticSieve.O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal OAI.CanonicalQuadraticSieve.O, originalPairLow I J W M K lengthScale) =
      ∑' B : {B : Ideal OAI.CanonicalQuadraticSieve.O // Admissible B},
        if (Ideal.absNorm B.val : ℝ) ≤ K then
          (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
            ∑' A : {A : Ideal OAI.CanonicalQuadraticSieve.O // Supported A},
              (idealZeroMask I (primaryGenerator A.val) * idealZeroMask J (primaryGenerator A.val)) *
                W (((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) / M)
        else 0 := by
  let F : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) → ℂ := fun p =>
    if (Ideal.absNorm p.2.val : ℝ) ≤ K then
      (idealZeroMask I (primaryGenerator p.1.val) * idealZeroMask J (primaryGenerator p.1.val)) *
      (quadraticRow I (primaryGenerator p.2.val) * quadraticRow J (primaryGenerator p.2.val)) *
      W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)) / M) else 0
  have hterm (p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) :
      originalPairLow I J W M K (p.1.val ^ 2 * p.2.val) = F p := by
    have hs : Supported (p.1.val ^ 2 * p.2.val) :=
      (supported_mul_iff _ _).mpr ⟨(supported_sq_iff _).mpr p.1.property, admissible_supported p.2.property⟩
    unfold originalPairLow
    rw [(squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2]
    by_cases hk : (Ideal.absNorm p.2.val : ℝ) ≤ K
    · rw [if_pos hk]
      unfold originalPairSource
      rw [if_pos hs, canonical_quadraticRow_star I hI,
        canonical_quadraticRow_primary_squarefree I hI, canonical_quadraticRow_primary_squarefree J hJ]
      simp only [F, if_pos hk, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
      ring
    · simp only [if_neg hk, F]
  have hsub : Summable (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => originalPairLow I J W M K lengthScale.val) :=
    (originalPairLow_summable I J W M K hM).subtype _
  have hp0 : Summable (fun p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B} =>
      originalPairLow I J W M K (p.1.val ^ 2 * p.2.val)) :=
    supportedSquarefreeEquiv.symm.summable_iff.mpr hsub
  have hp : Summable F := hp0.congr hterm
  have he : (∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, originalPairLow I J W M K lengthScale.val) =
      ∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale := by
    apply tsum_subtype_eq_of_support_subset
    intro lengthScale hL
    by_contra hs
    change ¬Supported lengthScale at hs
    exact hL (by simp [originalPairLow, originalPairSource, hs])
  calc
    _ = ∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, originalPairLow I J W M K lengthScale.val := he.symm
    _ = ∑' p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B},
        originalPairLow I J W M K (p.1.val ^ 2 * p.2.val) :=
      (supportedSquarefreeEquiv.symm.tsum_eq (fun lengthScale => originalPairLow I J W M K lengthScale.val)).symm
    _ = ∑' p, F p := tsum_congr hterm
    _ = ∑' p : {B : Ideal O // Admissible B} × {A : Ideal O // Supported A}, F (p.2, p.1) :=
      (Equiv.prodComm _ _).tsum_eq (fun p => F (p.2, p.1))
    _ = ∑' B : {B : Ideal O // Admissible B}, ∑' A : {A : Ideal O // Supported A}, F (A, B) :=
      hp.prod_symm.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      by_cases hk : (Ideal.absNorm B.val : ℝ) ≤ K
      · rw [if_pos hk, ← tsum_mul_left]
        apply tsum_congr
        intro A
        simp only [F, if_pos hk]
        ring
      · simp only [F, if_neg hk, tsum_zero]
end OAI.CanonicalQuadraticSieve
