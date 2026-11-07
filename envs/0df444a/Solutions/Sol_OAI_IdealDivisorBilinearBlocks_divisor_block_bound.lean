-- Prove2me | solution 1 for OAI.IdealDivisorBilinearBlocks.divisor_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:07:56.770048+00:00
-- url     : https://prove2.me/submissions/03d1c935-115b-4d09-8798-91c14c9bf105

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Theorems.Thm_OAI_IdealCoprimeBilinearSieve_ideal_coprime_bilinear_operator_bound
import Theorems.Thm_OAI_DivisorBlockCauchy_divisorConstant_pos
import Theorems.Thm_OAI_DivisorBlockCauchy_divisor_mask_energy_small_power
import Theorems.Thm_OAI_DivisorBlockCauchy_rectangular_cauchy
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_supportConstant_pos
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
open OAI.IdealDivisorBilinearBlocks
open FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy
namespace OAI.IdealDivisorBilinearBlocks
theorem _root_.solution {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (left : n → Ideal O) (right : p → Ideal O)
    (hl0 : ∀ j, left j ≠ 0) (hr0 : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hA : ∀ D ∈ S, ‖operator (A D)‖ ^ 2 ≤ UA)
    (hB : ∀ E ∈ T, ‖operator (B E)‖ ^ 2 ≤ UB) :
    (∑ D ∈ S, ∑ E ∈ T, blockValue left right A B a b D E) ^ 2 ≤
      (S.card : ℝ) * T.card *
        (UA * UB * (supportConstant ε hε * N₁ ^ ε) *
          (supportConstant ε hε * N₂ ^ ε)) *
        ((divisorConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by
  let EL (D : Ideal O) : ℝ := ∑ j, ‖if D ∣ left j then a j else 0‖ ^ 2
  let ER (E : Ideal O) : ℝ := ∑ k, ‖if E ∣ right k then b k else 0‖ ^ 2
  let C : ℝ := UA * UB * (supportConstant ε hε * N₁ ^ ε) *
    (supportConstant ε hε * N₂ ^ ε)
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hEL (D) : 0 ≤ EL D := by dsimp [EL]; positivity
  have hER (E) : 0 ≤ ER E := by dsimp [ER]; positivity
  have hp (D : Ideal O) (hD : D ∈ S) (E : Ideal O) (hE : E ∈ T) :
      (blockValue left right A B a b D E) ^ 2 ≤ C * EL D * ER E := by
    have hh := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound
      ε hε left right hl0 hr0 N₁ N₂ hN₁ hN₂ hlN hrN (A D) (B E)
      (fun j => if D ∣ left j then a j else 0)
      (fun k => if E ∣ right k then b k else 0)
    change (blockValue left right A B a b D E) ^ 2 ≤
      (‖operator (A D)‖ ^ 2 * (supportConstant ε hε * N₁ ^ ε) * EL D) *
      (‖operator (B E)‖ ^ 2 * (supportConstant ε hε * N₂ ^ ε) * ER E) at hh
    apply hh.trans
    calc
      _ ≤ (UA * (supportConstant ε hε * N₁ ^ ε) * EL D) *
          (UB * (supportConstant ε hε * N₂ ^ ε) * ER E) := by
        gcongr
        · exact hA D hD
        · exact hB E hE
      _ = _ := by dsimp [C]; ring
  have hc := rectangular_cauchy S T (blockValue left right A B a b) EL ER C hC hp
  have he1 := divisor_mask_energy_small_power ε hε S left hl0 N₁ hlN a
  have he2 := divisor_mask_energy_small_power ε hε T right hr0 N₂ hrN b
  apply hc.trans
  change (S.card : ℝ) * T.card * C * (∑ D ∈ S, EL D) * (∑ E ∈ T, ER E) ≤ _
  change (∑ D ∈ S, EL D) ≤ _ at he1
  change (∑ E ∈ T, ER E) ≤ _ at he2
  dsimp only [C]
  gcongr
end OAI.IdealDivisorBilinearBlocks
