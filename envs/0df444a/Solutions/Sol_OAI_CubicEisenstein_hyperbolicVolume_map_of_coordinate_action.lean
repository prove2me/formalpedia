-- Prove2me | solution 1 for OAI.CubicEisenstein.hyperbolicVolume_map_of_coordinate_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:04:48.707287+00:00
-- url     : https://prove2.me/submissions/a10557ec-b892-43aa-a48f-58a6e2a5ce16

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicVolume
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_euclideanToHyperbolic_measurable
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicEuclideanVolume_ae_positive

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (g : SL(2,ℂ))
    (f : EuclideanSpatial → EuclideanSpatial) (hf : Measurable f)
    (hvol : Measure.map f hyperbolicEuclideanVolume=hyperbolicEuclideanVolume)
    (hcompat : ∀p,0<p 2 → euclideanToHyperbolic (f p)=g • euclideanToHyperbolic p) :
    Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume := by
  unfold hyperbolicVolume
  rw [Measure.map_map (continuous_hyperbolic_action g).measurable euclideanToHyperbolic_measurable]
  calc
    _ = Measure.map (euclideanToHyperbolic ∘ f) hyperbolicEuclideanVolume := by
      apply Measure.map_congr
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      exact (hcompat p hp).symm
    _ = _ := by rw [←Measure.map_map euclideanToHyperbolic_measurable hf,hvol]
end OAI.CubicEisenstein
