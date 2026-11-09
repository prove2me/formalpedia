-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.hasSieveExponent_one_of_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:03:32.211197+00:00
-- url     : https://prove2.me/submissions/2b3dbf52-5b50-4c6f-883f-bdcd204ef4ee

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Theorems.Thm_OAI_CanonicalQuadraticSieve_hasSieveExponent_one_of_approximation
import Theorems.Thm_OAI_CanonicalQuadraticSieve_bootstrapExponent_gt_one
import Theorems.Thm_OAI_CanonicalQuadraticSieve_bootstrapExponent_le_two
import Theorems.Thm_OAI_CanonicalQuadraticSieve_bootstrapExponent_step
import Theorems.Thm_OAI_CanonicalQuadraticSieve_hasSieveExponent_two


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
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (himprove : ∀ α : ℝ, 1<α → α≤2 → HasSieveExponent α → HasSieveExponent (2-1/α)) :
    HasSieveExponent 1 := by
  have hn : ∀ n : ℕ, HasSieveExponent (bootstrapExponent n) := by
    intro n
    induction n with
    | zero => norm_num [bootstrapExponent]; exact hasSieveExponent_two
    | succ n ih =>
      rw [bootstrapExponent_step]
      exact himprove _ (bootstrapExponent_gt_one n) (bootstrapExponent_le_two n) ih
  apply hasSieveExponent_one_of_approximation
  intro η hη
  obtain ⟨n,hnη⟩ := exists_nat_one_div_lt hη
  refine ⟨bootstrapExponent n,?_,hn n⟩
  unfold bootstrapExponent
  linarith
end OAI.CanonicalQuadraticSieve
