-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.conjugateIdealRowSum_smoothed_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:12:10.290892+00:00
-- url     : https://prove2.me/submissions/a719da6c-6685-40f7-b4d5-0fa1673ec025

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_ConcretePrimeRowBridge_conjugateIdealRowSum_eq_star
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_pair_radial_poisson
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_smoothed_mean_square_expand


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
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonKernel F hFpos hFgood J I W scale := by
  simp_rw [conjugateIdealRowSum_eq_star, norm_star]
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  change (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
    (↑(‖∑ I ∈ F, star (mobiusIdealColumn C I) *
      finiteSquarefreeRow (fun i : primePool F => i.val) (primePool_good F hFgood)
        (idealSupport F I) y‖ ^ 2) : ℂ)) = _
  rw [finiteSquarefreeRow_smoothed_mean_square_expand
    (fun i : primePool F => i.val) (primePool_good F hFgood)
    F (idealSupport F) (fun I => star (mobiusIdealColumn C I)) W scale hscale,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteSquarefreeRow_pair_radial_poisson
    (fun i : primePool F => i.val) Subtype.val_injective (primePool_good F hFgood)
    hchar (idealSupport F J) (idealSupport F I) W scale hscale, star_star]
  rw [mul_comm (mobiusIdealColumn C J)]
  rfl
end OAI.ConcretePrimeRowBridge
