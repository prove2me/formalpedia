-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelEuclideanProjection_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:38:28.545258+00:00
-- url     : https://prove2.me/submissions/90671102-f15e-4bc6-93f0-dd695886e86b

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Theorems.Thm_OAI_CubicEisenstein_kernelEuclideanProjection_measurePreserving_on

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := hg.mono_measure (Measure.restrict_le_self (s := kernelEuclideanProjection '' S))
  rw [←hm.map_eq] at hh ⊢
  exact (integral_map hm.measurable.aemeasurable hh).symm
end OAI.CubicEisenstein
