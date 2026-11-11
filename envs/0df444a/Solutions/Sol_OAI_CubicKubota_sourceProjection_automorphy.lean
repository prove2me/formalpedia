-- Prove2me | solution 1 for OAI.CubicKubota.sourceProjection_automorphy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:59:47.636815+00:00
-- url     : https://prove2.me/submissions/7d73f4cd-1b9d-4f89-a4a5-c5b2599724e4

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedGaussSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_KubotaCharacter
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceProjection
import Theorems.Thm_OAI_CubicKubota_sourceSection_translate

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
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical MatrixGroups
open OAI.CubicKubota
open ActualEisensteinCubic
open CubicEisenstein
namespace OAI.CubicKubota
theorem _root_.solution (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w)
    (g : levelTwo) (w : HyperbolicSpace) :
    sourceProjection f (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter g * sourceProjection f w := by
  unfold sourceProjection
  simp_rw [sourceSection_translate f hf]
  rw [←Finset.mul_sum]
  rw [Function.Bijective.sum_comp
    (Group.mulRight_bijective (QuotientGroup.mk' levelThreeInTwo g))
    (fun q => f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w))]
  ring
end OAI.CubicKubota
