-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.divisor_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:16:41.730547+00:00
-- url     : https://prove2.me/submissions/be14806f-a73c-4638-a232-abd59b7ccd49

import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_LogDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_TwistedProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstCoreCutoff
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_divisor_pair
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorEnergyFactor_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorBlockCost_sqrt

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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open IdealCoprimeSieveOperator DivisorBlockCauchy
variable {n p : Type*} [Fintype n] [Fintype p]
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (h : HasSieveExponent α) :
    ∀ deltaLoss : ℝ, 0 < deltaLoss → ∃ C : ℝ, 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (M N D₁ D₂ : ℝ),
        1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
        ∀ (a : n → ℂ) (b : p → ℂ),
        Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) ≤
          divisorEnergyFactor ε hε N a b * (C * (M * N) ^ deltaLoss * (N + M ^ α * (D₁ * D₂))) := by
  intro deltaLoss hδ
  obtain ⟨C, hC, hc⟩ := h.divisor_pair deltaLoss hδ
  refine ⟨C, hC, ?_⟩
  intro ε hε M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N a b
  rw [divisorBlockCost_sqrt ε hε D₁ D₂ M N (by linarith) (by linarith) a b]
  exact mul_le_mul_of_nonneg_left (hc M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
