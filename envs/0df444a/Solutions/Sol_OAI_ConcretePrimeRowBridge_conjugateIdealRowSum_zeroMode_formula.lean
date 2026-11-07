-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.conjugateIdealRowSum_zeroMode_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:14:24.817279+00:00
-- url     : https://prove2.me/submissions/b9350071-2203-4ef9-8c46-cd6f3c4ef5dd

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_ConcretePrimeRowBridge_conjugateIdealRowSum_zeroMode_offDiagonal
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealPairPoissonZeroMode_diag


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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale) =
    (scale : ℂ) * paperRadialFourier W 0 *
      ∑ I ∈ F, (↑(‖mobiusIdealColumn C I‖ ^ 2) : ℂ) * idealPrimeDensity F I := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single I]
  · rw [idealPairPoissonZeroMode_diag, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    change (star _ * _) * _ = _ * ((star _ * _) * _)
    ring
  · intro J hJ hJI
    exact conjugateIdealRowSum_zeroMode_offDiagonal F hFpos hFgood C hI hJ hJI.symm W scale
  · exact fun h => (h hI).elim
end OAI.ConcretePrimeRowBridge
