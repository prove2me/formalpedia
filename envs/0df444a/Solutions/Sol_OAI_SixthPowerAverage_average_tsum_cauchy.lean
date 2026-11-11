-- Prove2me | solution 1 for OAI.SixthPowerAverage.average_tsum_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:51:37.782255+00:00
-- url     : https://prove2.me/submissions/6658df83-78ef-4110-b7fa-762fae228e98

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ThetaDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Theorems.Thm_OAI_SixthPowerAverage_averagingRows_card
import Theorems.Thm_OAI_SixthPowerAverage_average_tsum_eq_finite
import Theorems.Thm_OAI_SixthPowerAverage_sixth_power_average_cauchy


set_option autoImplicit false
open OAI
noncomputable section
open OAI.SixthPowerAverage
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
namespace OAI.SixthPowerAverage
theorem _root_.solution (V : 𝓢(ℝ,ℂ))
    (hV : ∀x,‖V x‖≤1)
    (hs : Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1)
    (hV0 : V 0=0) (Y : ℝ) (hY : 1≤Y) (A : ActualEisensteinCubic.O→ℂ) :
    ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*A (b^6)‖^2≤
      768*Y*∑z∈(averagingRows Y).image (fun b=>b^6),‖A z‖^2 := by
  rw [average_tsum_eq_finite V hs hV0 Y (by linarith) A]
  apply (sixth_power_average_cauchy _ _ _ (fun b hb=>hV _)).trans
  have hc:=averagingRows_card Y hY
  nlinarith [Finset.sum_nonneg (s:=(averagingRows Y).image (fun b=>b^6))
    (fun z _=>sq_nonneg ‖A z‖)]
end OAI.SixthPowerAverage
