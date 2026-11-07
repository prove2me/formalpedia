-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.canonical_divisor_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:28:29.663289+00:00
-- url     : https://prove2.me/submissions/b95d259c-0929-4a03-8823-3411311b76db

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_quotientMatrix_squared_norm_le
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_mono
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_nonneg
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_DescentFiberCost_finite_ideal_count_real
import Theorems.Thm_OAI_DivisorBlockCauchy_divisorConstant_pos
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_supportConstant_pos
import Theorems.Thm_OAI_IdealDivisorBilinearBlocks_divisor_block_bound
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
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤
      256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
        (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  have hS0 (D) (hD : D ∈ S) : D ≠ 0 := by
    intro hz
    have hh := (hS D hD).1
    simp only [hz, map_zero, Nat.cast_zero] at hh
    linarith
  have hT0 (E) (hE : E ∈ T) : E ≠ 0 := by
    intro hz
    have hh := (hT E hE).1
    simp only [hz, map_zero, Nat.cast_zero] at hh
    linarith
  have hA (D) (hD : D ∈ S) :
      ‖FiniteSieveOperator.operator (quotientMatrix D rows left)‖ ^ 2 ≤ sieveNorm M (N / D₁) := by
    apply (quotientMatrix_squared_norm_le D (hS0 D hD) rows left hr hl M N hrows hleft).trans
    exact sieveNorm_mono le_rfl (div_le_div_of_nonneg_left (by linarith) (by linarith) (hS D hD).1)
  have hB (E) (hE : E ∈ T) :
      ‖FiniteSieveOperator.operator (quotientMatrix E rows right)‖ ^ 2 ≤ sieveNorm M (N / D₂) := by
    apply (quotientMatrix_squared_norm_le E (hT0 E hE) rows right hr hri M N hrows hright).trans
    exact sieveNorm_mono le_rfl (div_le_div_of_nonneg_left (by linarith) (by linarith) (hT E hE).1)
  have hsCard := DescentFiberCost.finite_ideal_count_real S (2 * D₁) (by linarith)
    hS0 (fun D hD => (hS D hD).2)
  have htCard := DescentFiberCost.finite_ideal_count_real T (2 * D₂) (by linarith)
    hT0 (fun E hE => (hT E hE).2)
  have hh := divisor_block_bound ε hε S T left right (fun j => (hleft j).1.1)
    (fun k => (hright k).1.1) N N (by linarith) (by linarith)
    (fun j => (hleft j).2) (fun k => (hright k).2)
    (fun D => quotientMatrix D rows left) (fun E => quotientMatrix E rows right) a b
    (sieveNorm M (N / D₁)) (sieveNorm M (N / D₂)) (sieveNorm_nonneg _ _) (sieveNorm_nonneg _ _) hA hB
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  have hb1 := sieveNorm_nonneg M (N / D₁)
  have hb2 := sieveNorm_nonneg M (N / D₂)
  change (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤ _ at hh
  apply hh.trans
  calc
    _ ≤ (128 * (2 * D₁)) * (128 * (2 * D₂)) *
        (sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
          (supportConstant ε hε * N ^ ε) * (supportConstant ε hε * N ^ ε)) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N ^ ε) * ∑ k, ‖b k‖ ^ 2) := by gcongr
    _ = _ := by ring
end OAI.CanonicalQuadraticSieve
