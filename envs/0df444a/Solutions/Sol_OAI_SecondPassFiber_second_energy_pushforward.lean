-- Prove2me | solution 1 for OAI.SecondPassFiber.second_energy_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:05.019876+00:00
-- url     : https://prove2.me/submissions/1f39e77e-1b07-4fa0-b282-a10343d332c4

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_SecondPassFiber_valid_tuple_small_power
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_DescentWeightedCauchy_bounded_energy_pushforward
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
open scoped BigOperators
open OAI.SecondPassFiber
open scoped BigOperators Classical
open IdealMobiusDivisorSum ConcretePrimeRowBridge
namespace OAI.SecondPassFiber
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (P : Ideal O × O → ℂ) (B H : ℝ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ H →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ H) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (newLabel x, newRow x)‖ ^ 2) ≤
        B * C * (H * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P z‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := valid_tuple_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w P B H hb0 hB hH hvalid hmap ht hnorm hw
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward
    s t (fun x => (newLabel x, newRow x)) w P B hmap hw
  apply hpush.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hval : ∀ x ∈ s.filter (fun x => (newLabel x, newRow x) = z), Valid x z.1 b0 z.2 := by
    intro x hx
    have he := (Finset.mem_filter.mp hx).2
    have hv := hvalid x (Finset.mem_filter.mp hx).1
    have h1 : newLabel x = z.1 := congrArg Prod.fst he
    have h2 : newRow x = z.2 := congrArg Prod.snd he
    simpa only [h1, h2] using hv
  have hfiber := hc (s.filter (fun x => (newLabel x, newRow x) = z)) z.1 b0 z.2
    (ht z hz) hb0 hval
  have hgrowth : (Ideal.absNorm z.1 : ℝ) * Ideal.absNorm b0 ≤ H * Ideal.absNorm b0 :=
    mul_le_mul_of_nonneg_right (hnorm z hz) (by positivity)
  have hcard := hfiber.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hgrowth hε.le) hC.le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hB) (sq_nonneg ‖P z‖)
  simpa only [mul_assoc] using hterm
end OAI.SecondPassFiber
