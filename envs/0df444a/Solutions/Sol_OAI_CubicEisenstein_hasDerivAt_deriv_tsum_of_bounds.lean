-- Prove2me | solution 1 for OAI.CubicEisenstein.hasDerivAt_deriv_tsum_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:22:32.610877+00:00
-- url     : https://prove2.me/submissions/e31264e8-e693-419f-be84-38e72249a979

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalDifference
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SpatialDerivatives

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
open Filter
open scoped BigOperators Classical Topology
open Filter
open scoped BigOperators Classical Topology
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution {ι : Type*} (f : ι → ℝ → ℂ)
    (M₁ M₂ : ι → ℝ) (U : Set ℝ) (x : ℝ)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx : x ∈ U)
    (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hfirst : ∀i y, y∈U → DifferentiableAt ℝ (f i) y)
    (hsecond : ∀i y, y∈U → DifferentiableAt ℝ (deriv (f i)) y)
    (hbound₁ : ∀i y, y∈U → ‖deriv (f i) y‖≤M₁ i)
    (hbound₂ : ∀i y, y∈U → ‖deriv (deriv (f i)) y‖≤M₂ i)
    (hsum : Summable (fun i => f i x)) :
    HasDerivAt (deriv (fun y => ∑'i,f i y)) (∑'i,deriv (deriv (f i)) x) x := by
  have hfirstSum (y : ℝ) (hy : y∈U) :=
    hasDerivAt_tsum_of_isPreconnected hM₁ hU hUc
      (fun i z hz => (hfirst i z hz).hasDerivAt) hbound₁ hx hsum hy
  have hsumFirst : Summable (fun i => deriv (f i) x) :=
    Summable.of_norm_bounded hM₁ (fun i => hbound₁ i x hx)
  have hsecondSum := hasDerivAt_tsum_of_isPreconnected hM₂ hU hUc
    (fun i z hz => (hsecond i z hz).hasDerivAt) hbound₂ hx hsumFirst hx
  apply hsecondSum.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (hfirstSum y hy).deriv
end OAI.CubicEisenstein
