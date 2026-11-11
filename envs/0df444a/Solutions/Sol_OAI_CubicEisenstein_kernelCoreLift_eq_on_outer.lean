-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelCoreLift_eq_on_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:05:18.705176+00:00
-- url     : https://prove2.me/submissions/8ba82c82-b280-4d83-9610-9fd6ccfd1463

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactEnergyFamilies
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialProfiles
import Theorems.Thm_OAI_CubicEisenstein_kernelCoreLift_eventually_eq
import Theorems.Thm_OAI_CubicEisenstein_kernelChartCore_subset


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    Set.EqOn (kernelCoreLift χ f) (kernelTestField f) (tsupport χ.func) := by
  intro p hp
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).self_of_nhds
  · have hz : kernelTestField f p=0 := by
      change f.1 (kernelEuclideanProjection p)=0
      apply image_eq_zero_of_notMem_tsupport
      intro hfp
      obtain ⟨q,hq,heq⟩ := hf hfp
      have hqp := hinj (kernelChartCore_subset χ hq) hp heq
      exact hc (hqp ▸ hq)
    change (kernelFullCutoff χ).func p • kernelTestField f p=kernelTestField f p
    rw [hz,smul_zero]
end OAI.CubicEisenstein
