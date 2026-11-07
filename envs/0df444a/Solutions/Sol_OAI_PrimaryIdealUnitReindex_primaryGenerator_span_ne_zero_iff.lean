-- Prove2me | solution 1 for OAI.PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:58:01.170682+00:00
-- url     : https://prove2.me/submissions/2bec67ef-0284-44ad-b590-c00ad3097675

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_PrimaryIdealUnitReindex_lambda_prime_actual
import Theorems.Thm_OAI_PrimaryIdealUnitReindex_primaryGenerator_ne_zero_of_good_factors
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
open scoped BigOperators Classical
open OAI.PrimaryIdealUnitReindex
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
namespace OAI.PrimaryIdealUnitReindex
theorem _root_.solution (z : O) :
    primaryGenerator (Ideal.span {z}) ≠ 0 ↔ ¬ lambda ∣ z := by
  constructor
  · intro hg hdiv
    have hs := primaryGenerator_spec (Ideal.span {z}) hg
    have hzgen : z ∣ primaryGenerator (Ideal.span {z}) := by
      apply Ideal.mem_span_singleton.mp
      exact hs.1.le (Ideal.subset_span (by simp))
    have hgen := hdiv.trans hzgen
    have hminus : lambda ∣ primaryGenerator (Ideal.span {z}) - 1 :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans hs.2
    have hone : lambda ∣ (1 : O) := by
      convert dvd_sub hgen hminus using 1 ; ring
    exact lambda_prime_actual.not_isUnit (isUnit_of_dvd_one hone)
  · intro hdiv
    have hz : z ≠ 0 := by intro h; subst z; exact hdiv (dvd_zero _)
    have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
    apply primaryGenerator_ne_zero_of_good_factors _ hI
    intro P hP hlam
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hzin : z ∈ P := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
      (Ideal.subset_span (by simp))
    have hcop : IsCoprime lambda z := lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hdiv
    obtain ⟨a, b, hab⟩ := hcop
    have hone : (1 : O) ∈ P := by
      rw [← hab]
      exact P.add_mem (P.mul_mem_left a hlam) (P.mul_mem_left b hzin)
    exact (inferInstance : P.IsMaximal).ne_top ((Ideal.eq_top_iff_one P).mpr hone)
end OAI.PrimaryIdealUnitReindex
