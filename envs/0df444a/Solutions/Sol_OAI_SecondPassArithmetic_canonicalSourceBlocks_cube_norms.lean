-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalSourceBlocks_cube_norms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:47:30.465545+00:00
-- url     : https://prove2.me/submissions/f52135ee-997a-4c2f-b87a-2e480a75c149

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
theorem _root_.solution
    (p:ι→O) (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (B:ℝ)
    (hleft:∀b∈bs,‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hright:∀b∈bs,‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs):
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct p q.cube.support q.cube.leftExponent)‖^2≤B ∧
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p q.cube.support q.cube.rightExponent)‖^2≤B := by
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  change ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.swap.support b.rightExponent)‖^2≤B ∧
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.swap.support b.leftExponent)‖^2≤B
  rw [cube_swap_support]
  exact ⟨hright b hb,hleft b hb⟩
end OAI.SecondPassArithmetic
