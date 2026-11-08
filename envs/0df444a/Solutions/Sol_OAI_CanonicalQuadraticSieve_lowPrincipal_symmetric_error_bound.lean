-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.lowPrincipal_symmetric_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:34:09.425871+00:00
-- url     : https://prove2.me/submissions/0b18166e-6580-491e-96c8-81daf070dc3e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspIntegration
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MaskedPrincipalBounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_lowPrincipalError_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_symmetric_truncation_scalar_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_symmetric_truncation_scales
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_supportConstant_pos


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
open ActualEisensteinCubic
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (I J : Ideal O) (_hI : Admissible I) (_hJ : Admissible J)
        (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖lowPrincipalError I J W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := lowPrincipalError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ε hε I J hI hJ W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hh := hb ε hε I J hI hJ W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  have hc := (supportConstant_pos ε hε).le
  calc
    _ ≤ (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hh
    _ ≤ (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring
end OAI.CanonicalQuadraticSieve
