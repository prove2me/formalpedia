-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.masked_principal_radial_poisson_zero_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:56:59.420309+00:00
-- url     : https://prove2.me/submissions/ebf71d82-de6c-483f-8146-b6ba8b82554b

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_masked_principal_radial_poisson
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubset_moebius_norm_sum
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_lattice_summable_norm
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
      (M : ℂ) * paperRadialFourier V 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) +
        maskedPrincipalRemainder P S V M := by
  have hp (E : Finset ι) : 0 < (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hs (E : Finset ι) :
      (∑' h : O, paperRadialFourier V
        (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))) =
      paperRadialFourier V 0 +
        ∑' h : O, if h = 0 then 0 else paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
    have hsum := (paperRadialFourier_lattice_summable_norm V
      (M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) (div_pos hM (hp E))).of_norm
    have heq (h : O) : M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) * ‖eisEmbedding h‖ ^ 2 =
        M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by ring
    simp_rw [heq] at hsum
    simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
      using hsum.tsum_eq_add_tsum_ite 0
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  rw [masked_principal_radial_poisson P hinj S V M hM]
  simp_rw [hs, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
  rw [primeSubset_moebius_norm_sum P hprime hinj S]
  unfold maskedPrincipalRemainder
  ring
end OAI.ActualEisensteinCubic
