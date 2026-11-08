-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:26:08.773177+00:00
-- url     : https://prove2.me/submissions/10fcfd89-1157-46b3-ae29-fd9cb4cb834c

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedDefects
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_GlobalEncoding
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondTuple_cube_eq
import Theorems.Thm_OAI_FirstCauchyArithmetic_family_product_injective


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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj
namespace OAI.SecondPassArithmetic
theorem _root_.solution {x y : GlobalSecondData ι}
    (hx : GlobalSecondAdmissible x) (hy : GlobalSecondAdmissible y)
    (ht : globalSecondFixedTriple p x=globalSecondFixedTriple p y)
    (h : globalSecondTuple p x=globalSecondTuple p y) : x=y := by
  have hc := globalSecondTuple_cube_eq p hinj hx.1 hy.1 h
  have hA := congrArg (fun q : Ideal O × Ideal O × Ideal O => q.2.1) ht
  have hR := congrArg (fun q : Ideal O × Ideal O × Ideal O => q.2.2) ht
  have hC := congrArg (fun z : SecondPassFiber.OldTuple => z.core 1) h
  have hD := congrArg (fun z : SecondPassFiber.OldTuple => z.core 7) h
  have hE := congrArg (fun z : SecondPassFiber.OldTuple => z.core 2) h
  have hV := congrArg SecondPassFiber.OldTuple.v h
  have hk := congrArg SecondPassFiber.OldTuple.row h
  have hA' : x.firstCommon=y.firstCommon := FirstCauchyArithmetic.family_product_injective _ hinj hA
  have hC' : x.common=y.common := FirstCauchyArithmetic.family_product_injective _ hinj hC
  have hD' : x.firstDivisor=y.firstDivisor := FirstCauchyArithmetic.family_product_injective _ hinj hD
  have hE' : x.source.divisor=y.source.divisor := FirstCauchyArithmetic.family_product_injective _ hinj hE
  have hV' : x.source.overlap=y.source.overlap := FirstCauchyArithmetic.family_product_injective _ hinj hV
  have hR' : x.source.sourceCommon\x.source.divisor=y.source.sourceCommon\y.source.divisor :=
    FirstCauchyArithmetic.family_product_injective _ hinj hR
  have hG : x.source.sourceCommon=y.source.sourceCommon := by
    calc
      _ = x.source.divisor ∪ (x.source.sourceCommon\x.source.divisor) :=
        (Finset.union_sdiff_of_subset hx.2.1).symm
      _ = y.source.divisor ∪ (y.source.sourceCommon\y.source.divisor) := by rw [hR',hE']
      _ = _ := Finset.union_sdiff_of_subset hy.2.1
  exact GlobalSecondData.ext hc hA' hC' hD' (SecondExpansionData.ext hG hE' hV' hk)
end OAI.SecondPassArithmetic
