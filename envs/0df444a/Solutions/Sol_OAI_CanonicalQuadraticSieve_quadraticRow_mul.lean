-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.quadraticRow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:12:37.352244+00:00
-- url     : https://prove2.me/submissions/a6e2d4c0-d4ed-49ba-901c-aee92f494cec

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_of_dvd
import Theorems.Thm_OAI_CanonicalQuadraticSieve_quadraticRow_eq
import Theorems.Thm_OAI_ConcretePrimeRowBridge_mem_idealSupport_iff
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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ConcretePrimeRowBridge ActualEisensteinCubic
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (I J : Ideal O) (hIJ : Admissible (I * J)) (z : O) :
    quadraticRow (I * J) z = quadraticRow I z * quadraticRow J z := by
  have hI : Admissible I := admissible_of_dvd hIJ (dvd_mul_right I J)
  have hJ : Admissible J := admissible_of_dvd hIJ (dvd_mul_left J I)
  let F : Finset (Ideal O) := {I, J, I * J}
  have hF : ∀ K ∈ F, Admissible K := by
    intro K hK
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · exact hI
    · exact hJ
    · exact hIJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  have hIJF : I * J ∈ F := by simp [F]
  have hu : idealSupport F (I * J) = idealSupport F I ∪ idealSupport F J := by
    ext P
    simp only [mem_idealSupport_iff, UniqueFactorizationMonoid.normalizedFactors_mul hI.1 hJ.1,
      Multiset.mem_add, Finset.mem_union]
  have hd : Disjoint (idealSupport F I) (idealSupport F J) := by
    apply Finset.disjoint_left.mpr
    intro P hPI hPJ
    have hpI := (mem_idealSupport_iff F I P).mp hPI
    have hpJ := (mem_idealSupport_iff F J P).mp hPJ
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val hpI
    have hi : P.val ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpI
    have hj : P.val ∣ J := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpJ
    exact hp.not_isUnit ((IsRelPrime.of_squarefree_mul hIJ.2.1) hi hj)
  rw [quadraticRow_eq F hF (I * J) hIJF z, quadraticRow_eq F hF I hIF z,
    quadraticRow_eq F hF J hJF z]
  unfold idealSexticRow finiteSquarefreeRow
  rw [hu, Finset.prod_union hd, mul_pow]
end OAI.CanonicalQuadraticSieve
