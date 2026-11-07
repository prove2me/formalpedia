-- Prove2me | solution 1 for OAI.QuadraticInitialBound.divisor_conductor_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:32:00.204808+00:00
-- url     : https://prove2.me/submissions/8a433030-7ab5-4ab7-b1b1-d8f257f1a590

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Theorems.Thm_OAI_QuadraticInitialBound_supportNorm_nonneg
import Theorems.Thm_OAI_QuadraticInitialBound_two_pow_card_le_supportNorm
import Theorems.Thm_OAI_ActualEisensteinCubic_activePrimeModulus_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_activeSupport_product_mul_common_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
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
open OAI.QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.QuadraticInitialBound
theorem _root_.solution {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S T : Finset α)
    (N : ℝ) (hN : 0 ≤ N) (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N) :
    (2 : ℝ) ^ (S ∩ T).card *
      ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ≤ N := by
  have hid := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
    (activeSupport_product_mul_common_sq P S T)
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hid
  rw [← activePrimeModulus_norm_sq] at hid
  change ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 *
    (supportNorm P (S ∩ T)) ^ 2 = supportNorm P S * supportNorm P T at hid
  have hpow := two_pow_card_le_supportNorm P (S ∩ T)
  have hmul := mul_le_mul_of_nonneg_right hpow
    (norm_nonneg (eisEmbedding (finitePrimeModulus (activePrimes P S T))))
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ (S ∩ T).card *
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) hmul 2
  have hprod := mul_le_mul hS hT (supportNorm_nonneg P T) hN
  nlinarith
end OAI.QuadraticInitialBound
