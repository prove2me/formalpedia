-- Prove2me | solution 1 for OAI.SecondPassArithmetic.sum_globalFirstFamilySet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:49:25.545095+00:00
-- url     : https://prove2.me/submissions/259c8348-f869-4c8a-99d1-89c265e00eee

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks

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
open OAI.SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open RayFourExpansion (RayCharacter crossCoeff)
variable {ι : Type*} [DecidableEq ι]
namespace OAI.SecondPassArithmetic
theorem _root_.solution {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (f : GlobalFirstData ι → M) :
    ∑ d∈globalFirstFamilySet pool blocks,f d =
      ∑ b∈blocks,∑ A∈(globalCubePool pool b).powerset,f (b.withCommon A) := by
  unfold globalFirstFamilySet
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro A hA B hB he
    exact congrArg GlobalFirstData.firstCommon he
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨B,hB,he⟩ := Finset.mem_image.mp hy
    exact hne (congrArg GlobalFirstData.block he).symm
end OAI.SecondPassArithmetic
