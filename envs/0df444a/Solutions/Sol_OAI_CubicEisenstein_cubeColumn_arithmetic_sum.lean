-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeColumn_arithmetic_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:56:59.083203+00:00
-- url     : https://prove2.me/submissions/ccc841a0-4012-4418-bc40-51c18c7eb7e9

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalTruncation
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FrequencyCutoffs
import Theorems.Thm_OAI_CubicEisenstein_cubeColumn_expanded
import Theorems.Thm_OAI_CubicEisenstein_arithmeticResidueSum_cube
import Theorems.Thm_OAI_CubicEisenstein_card_admissible_cube_product
import Theorems.Thm_OAI_CubicEisenstein_primary_coprime_three


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
open scoped BigOperators Classical
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
namespace OAI.CubicEisenstein
theorem _root_.solution (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticResidueSum 0 (cubeColumn b n I)=
      (3^(3*(n+1))*Ideal.absNorm I.1^2*idealTotient I.1:ℕ) := by
  have ha : cubeSign b*cubeBase n I ≠ 0 :=
    mul_ne_zero (cubeSign_isUnit b).ne_zero (cubeBase_ne_zero n I)
  have hA := arithmeticResidueSum_cube _ ha
  rw [← cubeColumn_cube] at hA
  rw [hA,cubeColumn_expanded]
  have hc : IsCoprime (cubeSign b*primaryGenerator I.1) (3:O) :=
    (isCoprime_mul_unit_left_left (cubeSign_isUnit b) _ _).mpr
      (primary_coprime_three _ (primaryGenerator_spec I.1 I.2).2)
  have hs : Ideal.span {cubeSign b*primaryGenerator I.1}=I.1 := by
    rw [Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),(primaryGenerator_spec I.1 I.2).1]
  rw [card_admissible_cube_product (n+1) _ (mul_ne_zero (cubeSign_isUnit b).ne_zero I.2) hc,hs]
end OAI.CubicEisenstein
