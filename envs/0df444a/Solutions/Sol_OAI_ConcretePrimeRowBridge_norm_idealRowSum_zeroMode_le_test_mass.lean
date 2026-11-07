-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.norm_idealRowSum_zeroMode_le_test_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:28.601967+00:00
-- url     : https://prove2.me/submissions/8db38278-ac7c-4e4c-8451-251293c916a6

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Theorems.Thm_OAI_ConcretePrimeRowBridge_norm_idealRowSum_zeroMode_le
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_baseChangeWeight_le_one

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
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale‖ ≤
    (|scale| * ‖paperRadialFourier W 0‖) *
      ∑ I ∈ F, ‖A (Ideal.absNorm I)‖ ^ 2 := by
  refine (norm_idealRowSum_zeroMode_le F hFpos hFgood χ A W scale).trans ?_
  gcongr with I hI
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_baseChangeWeight_le_one χ I)
end OAI.ConcretePrimeRowBridge
