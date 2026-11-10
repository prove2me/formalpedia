-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelProjection_measurePreserving_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:26:06.217177+00:00
-- url     : https://prove2.me/submissions/b4c051a6-fb56-46f9-bcde-8ccc90382b95

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Theorems.Thm_OAI_CubicEisenstein_kernelProjection_measure_image
import Theorems.Thm_OAI_CubicEisenstein_measurable_integralOrbitProjection


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
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (U : Set HyperbolicSpace) (hU : MeasurableSet U)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) U) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict U)
      ((integralQuotientVolume globalKubotaKernel).restrict (integralOrbitProjection globalKubotaKernel '' U)) := by
  refine ⟨measurable_integralOrbitProjection _,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.restrict_apply hB]
  have hset : B∩(integralOrbitProjection globalKubotaKernel '' U)=
      integralOrbitProjection globalKubotaKernel '' (integralOrbitProjection globalKubotaKernel ⁻¹' B∩U) := by
    ext q
    constructor
    · rintro ⟨hq,w,hw,rfl⟩
      exact ⟨w,⟨hq,hw⟩,rfl⟩
    · rintro ⟨w,⟨hw,hu⟩,rfl⟩
      exact ⟨hw,⟨w,hu,rfl⟩⟩
  rw [hset,kernelProjection_measure_image _ (((measurable_integralOrbitProjection _) hB).inter hU)
    (hinj.mono Set.inter_subset_right)]
end OAI.CubicEisenstein
