-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.maskedPrincipalRemainder_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:46:49.363777+00:00
-- url     : https://prove2.me/submissions/7a90abc2-8ed0-42a7-9d15-01ea9dde6c38

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_nonzero_sum_uniform
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_norm_sq
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
import Theorems.Thm_OAI_QuadraticInitialBound_norm_ideal_moebius_le_one
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
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖maskedPrincipalRemainder P S W M‖ ≤ (2 : ℝ) ^ S.card * pvControl W := by
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) : M * ‖f E‖ ≤ pvControl W := by
    have ht := paperRadialFourier_nonzero_sum_uniform W (M / n E) (div_pos hM (hn E))
    have he (h : O) : M / n E * ‖eisEmbedding h‖ ^ 2 = M * ‖eisEmbedding h‖ ^ 2 / n E := by ring
    simp only [he] at ht
    have hm := norm_ideal_moebius_le_one (∏ i ∈ E, P i)
    dsimp only [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    calc
      _ = ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ((M / n E) * ‖∑' h : O, if h = 0 then 0 else
            paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)‖) := by dsimp [n]; ring
      _ ≤ 1 * pvControl W := mul_le_mul hm ht (by positivity) zero_le_one
      _ = _ := one_mul _
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ = ∑ E ∈ S.powerset, M * ‖f E‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ E ∈ S.powerset, pvControl W := Finset.sum_le_sum (fun E _ => hf E)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
end OAI.EisensteinSchwartzPoisson
