-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.original_middle_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:03:03.377639+00:00
-- url     : https://prove2.me/submissions/7361e448-c7e9-4d87-9ab3-93193f9f1431

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SpatialDerivatives
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstCoreCutoff
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_LatticeEnvelopes
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_nonzeroLatticeEnvelopeConstant_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_originalMiddleDecayConstant_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_actual_original_middle_all_frequencies
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorExponentConstant_pos
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisor_cost_with_constant
import Theorems.Thm_OAI_CanonicalQuadraticSieve_original_middle_scale_shape
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorEnergyFactor_nonneg


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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal OAI.CanonicalQuadraticSieve.O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal OAI.CanonicalQuadraticSieve.O) (left : n → Ideal OAI.CanonicalQuadraticSieve.O) (right : p → Ideal OAI.CanonicalQuadraticSieve.O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : OAI.CanonicalQuadraticSieve.O → n → ℂ) (b : OAI.CanonicalQuadraticSieve.O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * Real.sqrt (M / B)) :
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + U * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a₀ b₀
  have hs := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (originalMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc hk)
    _ = ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          (N + B ^ α * (D₁ * D₂)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (original_middle_scale_shape M B N (D₁ * D₂) U α hM.le (by linarith) hcut) (by positivity)
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
