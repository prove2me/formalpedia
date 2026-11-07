-- Prove2me | solution 1 for OAI.CubicRamified.primary_card_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:36.896195+00:00
-- url     : https://prove2.me/submissions/3a46cb73-9465-4152-8c8b-cbaf27a9fd41

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi

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
open scoped BigOperators Classical
open OAI.CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
namespace OAI.CubicRamified
theorem _root_.solution (N : ℕ) (A B : ℤ) (hN : 1 < N)
    (hn : (N : ℤ) = 1 + 9*(A^2-A*B+B^2)+3*(2*A-B)) :
    ((N-1)/3)%3 = ((2*A-B)%3).toNat %3 := by
  have hsub : ((N-1 : ℕ) : ℤ) = (N : ℤ)-1 := by omega
  have hdiv : (((N-1)/3 : ℕ) : ℤ) = 3*(A^2-A*B+B^2)+(2*A-B) := by
    rw [Int.natCast_ediv, hsub]
    have hh : (N : ℤ)-1 = 3*(3*(A^2-A*B+B^2)+(2*A-B)) := by omega
    rw [hh]
    omega
  have hrem : (((2*A-B)%3).toNat : ℤ) = (2*A-B)%3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  omega
end OAI.CubicRamified
