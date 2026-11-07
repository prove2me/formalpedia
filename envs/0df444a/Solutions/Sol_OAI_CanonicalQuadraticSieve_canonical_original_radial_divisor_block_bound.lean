-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.canonical_original_radial_divisor_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:38:17.31962+00:00
-- url     : https://prove2.me/submissions/79445f9a-214d-49e9-97bf-42d78686a998

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
import Theorems.Thm_OAI_QuadraticKernelTransfer_radial_matrix_kernel_transfer
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_original_divisor_block_phase_bound
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
open scoped BigOperators Classical
open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (W : 𝓢(ℝ, ℂ)) (L₁ L₂ L₃ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ M N : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hN : 1 ≤ N)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (x : S → T → m → ℝ) (y : n → ℝ) (z : p → ℝ),
        (∀ D E i, |x D E i| ≤ L₁) → (∀ j, |y j| ≤ L₂) → (∀ k, |z k| ≤ L₃) →
        (1 + R) ^ A * (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
          originalTerm rows left right a b D.val E.val i j k *
            paperRadialFourier W (R * Real.exp (x D E i + (y j + z k)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  obtain ⟨C, hC, hker⟩ := radial_matrix_kernel_transfer W L₁ (L₂ + L₃) hL₁ (add_nonneg hL₂ hL₃) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n p _ _ _ _ _ _ ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b x y z hx hy hz
  let c : (S × T × m) → (n × p) → ℂ := fun i j =>
    originalTerm rows left right a b i.1.val i.2.1.val i.2.2 j.1 j.2
  have hp (t : ℝ) : (∑ i : S × T × m, ‖∑ j : n × p, c i j * logPhase t (y j.1 + z j.2)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
    have hb := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
      rows left right hr hl hri hrows hleft hright a b y z t
    simp only [c, Fintype.sum_prod_type]
    let v : Ideal O → Ideal O → ℝ := fun D E => ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖
    change (∑ D : S, ∑ E : T, v D.val E.val) ≤ _
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, v D E.val)]
    have he (D : Ideal O) := Finset.sum_coe_sort T (v D)
    simp_rw [he]
    exact hb
  have hb := hker R hR c (fun i => x i.1 i.2.1 i.2.2) (fun j => y j.1 + z j.2)
    (Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b)) (Real.sqrt_nonneg _)
    (fun i => hx i.1 i.2.1 i.2.2)
    (fun j => (abs_add_le _ _).trans (add_le_add (hy j.1) (hz j.2))) hp
  simpa only [c, Fintype.sum_prod_type] using hb
end OAI.CanonicalQuadraticSieve
