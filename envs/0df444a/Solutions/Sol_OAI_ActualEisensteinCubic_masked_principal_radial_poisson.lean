-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.masked_principal_radial_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:53:41.72317+00:00
-- url     : https://prove2.me/submissions/d2a7ad1a-1b12-4c86-862e-ab86fa8fa494

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalNormalizedGauss_of_isEmpty
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_masked_radial_poisson_collected
import Theorems.Thm_OAI_ActualEisensteinCubic_finitePrimeModulus_norm_of_isEmpty
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_of_isEmpty
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



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
open scoped BigOperators Classical SchwartzMap
open OAI.ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson
namespace OAI.ActualEisensteinCubic
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * ∑ E ∈ S.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
        ∑' h : O, paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
  let Q : Empty → Ideal O := Empty.elim
  let : ∀ i, (Q i).IsMaximal := fun i => nomatch i
  have hcop : Pairwise (Function.onFun IsCoprime Q) := by intro i; cases i
  have hg : ∀ i, lambda ∉ Q i := fun i => nomatch i
  have hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2 := fun i => nomatch i
  have hj0 : ∀ i : Empty, (1 : ℕ) ≠ 0 := fun i => nomatch i
  have hj6 : ∀ i : Empty, (1 : ℕ) < 6 := fun i => nomatch i
  have hp := canonical_masked_radial_poisson_collected P hinj S Q hcop hg hc
    (fun _ => 1) hj0 hj6 V M hM
  simpa only [finiteSexticRow_of_isEmpty, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    star_one, one_mul, one_pow, primeSubsetGenerator_norm_sq, Complex.ofReal_natCast] using hp
end OAI.ActualEisensteinCubic
