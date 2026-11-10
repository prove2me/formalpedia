-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelEuclideanProjection_volume_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:38:27.391729+00:00
-- url     : https://prove2.me/submissions/f7fe12d4-5c04-405d-8d5b-89151d52c285

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HarmonicAggregation
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Theorems.Thm_OAI_CubicEisenstein_euclideanVolume_le_heightCube_hyperbolic
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv
namespace OAI.CubicEisenstein
theorem _root_.solution (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) (g : KernelQuotient→ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) :
    IntegrableOn (fun p => g (kernelEuclideanProjection p)) S volume := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := (hm.integrable_comp_of_integrable hg.integrableOn).smul_measure
    (c := ENNReal.ofReal (b^3)) ENNReal.ofReal_ne_top
  exact hh.mono_measure (euclideanVolume_le_heightCube_hyperbolic S hS hpos b hb hheight)
end OAI.CubicEisenstein
