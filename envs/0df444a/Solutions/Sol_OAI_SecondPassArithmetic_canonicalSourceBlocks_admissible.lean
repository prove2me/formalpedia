-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalSourceBlocks_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:47:29.202628+00:00
-- url     : https://prove2.me/submissions/3e5046ec-5a39-4728-8151-1ff606f1e0a6

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DualZeroMode
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceBlocks_mem
import Theorems.Thm_OAI_SecondPassArithmetic_cube_swap_support


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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
variable {ι:Type*} [DecidableEq ι]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (pool:Finset ι) (bs:Finset (CubeCoordinates ι))
    (hadm:∀b∈bs,b.Admissible) (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs):
    GlobalCubeAdmissible q := by
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  have ha:=hadm b hb
  constructor
  · constructor
    · change b.rightDivisor⊆b.swap.support
      rw [cube_swap_support]
      exact ha.2
    · change b.leftDivisor⊆b.swap.support
      rw [cube_swap_support]
      exact ha.1
  constructor
  · change Disjoint C b.swap.support
    rw [cube_swap_support]
    exact Finset.disjoint_left.mpr (fun i hi hbi=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hbi)
  · change D⊆C∪b.swap.support
    rw [cube_swap_support]
    exact (Finset.mem_powerset.mp hD).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))
end OAI.SecondPassArithmetic
