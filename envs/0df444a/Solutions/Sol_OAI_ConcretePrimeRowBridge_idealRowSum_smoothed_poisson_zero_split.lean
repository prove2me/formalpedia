-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.idealRowSum_smoothed_poisson_zero_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:50.493875+00:00
-- url     : https://prove2.me/submissions/5fbe38fb-29e3-464a-921f-aeab43ae5a69

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealRowSum_zeroMode_formula
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealPairPoissonKernel_zero_split
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealRowSum_smoothed_poisson


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
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) =
    (scale : ℂ) * paperRadialFourier W 0 *
      (∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
        idealPrimeDensity F I) +
      ∑ I ∈ F, ∑ J ∈ F,
        (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
          (baseChangeWeight χ J * A (Ideal.absNorm J))) *
        idealPairPoissonNonzeroMode F hFpos hFgood I J W scale := by
  rw [idealRowSum_smoothed_poisson F hFpos hFgood hchar χ A W scale hscale]
  simp_rw [idealPairPoissonKernel_zero_split F hFpos hFgood _ _ W scale hscale,
    mul_add, Finset.sum_add_distrib]
  rw [idealRowSum_zeroMode_formula F hFpos hFgood χ A W scale]
end OAI.ConcretePrimeRowBridge
