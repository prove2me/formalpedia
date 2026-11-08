-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondTuple_cube_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:21:48.847345+00:00
-- url     : https://prove2.me/submissions/8cb81daf-b7ad-4452-89eb-07bd3189caf6

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedDefects
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_GlobalEncoding
import Theorems.Thm_OAI_SecondPassArithmetic_primeProduct_span_exponents_eq
import Theorems.Thm_OAI_SecondPassArithmetic_CubeCoordinates_left_off
import Theorems.Thm_OAI_SecondPassArithmetic_CubeCoordinates_right_off
import Theorems.Thm_OAI_SecondPassArithmetic_CubeCoordinates_aLabel_left
import Theorems.Thm_OAI_SecondPassArithmetic_CubeCoordinates_aLabel_right
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
    (hx : x.cube.Admissible) (hy : y.cube.Admissible)
    (h : globalSecondTuple p x=globalSecondTuple p y) : x.cube=y.cube := by
  have h₁ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 4) h
  have h₂ := congrArg SecondPassFiber.OldTuple.b2 h
  have hA₁ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 5) h
  have hA₂ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 6) h
  change Ideal.span {primeProduct p x.cube.support x.cube.leftExponent} =
    Ideal.span {primeProduct p y.cube.support y.cube.leftExponent} at h₁
  change Ideal.span {primeProduct p x.cube.support x.cube.rightExponent} =
    Ideal.span {primeProduct p y.cube.support y.cube.rightExponent} at h₂
  have hv₁ := primeProduct_span_exponents_eq p hinj x.cube.support y.cube.support
    x.cube.leftExponent y.cube.leftExponent x.cube.left_off y.cube.left_off h₁
  have hv₂ := primeProduct_span_exponents_eq p hinj x.cube.support y.cube.support
    x.cube.rightExponent y.cube.rightExponent x.cube.right_off y.cube.right_off h₂
  change Ideal.span {aLabel p x.cube.support x.cube.leftBit} =
    Ideal.span {aLabel p y.cube.support y.cube.leftBit} at hA₁
  change Ideal.span {aLabel p x.cube.support x.cube.rightBit} =
    Ideal.span {aLabel p y.cube.support y.cube.rightBit} at hA₂
  rw [CubeCoordinates.aLabel_left p x.cube hx,CubeCoordinates.aLabel_left p y.cube hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA₁
  rw [CubeCoordinates.aLabel_right p x.cube hx,CubeCoordinates.aLabel_right p y.cube hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA₂
  apply CubeCoordinates.ext
  · exact Finsupp.ext (congrFun hv₁)
  · exact Finsupp.ext (congrFun hv₂)
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hA₁
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hA₂
end OAI.SecondPassArithmetic
