-- Prove2me | solution 1 for OAI.FiniteSieveRestriction.row_restriction_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:11:54.816204+00:00
-- url     : https://prove2.me/submissions/ed087dd6-773f-478d-a9fb-ccf9382dcff7

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Theorems.Thm_OAI_FiniteSieveRestriction_column_restriction_norm_le
import Theorems.Thm_OAI_FiniteSieveOperator_operator_conjTranspose_norm


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
open OAI.FiniteSieveRestriction
open FiniteSieveOperator
variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
namespace OAI.FiniteSieveRestriction
theorem _root_.solution {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix p m ℂ) :
    ‖operator (fun i j => A (f i) j)‖ ≤ ‖operator A‖ := by
  let B : Matrix n m ℂ := fun i j => A (f i) j
  have h := column_restriction_norm_le f hf A.conjTranspose
  change ‖operator B.conjTranspose‖ ≤ ‖operator A.conjTranspose‖ at h
  rw [operator_conjTranspose_norm B, operator_conjTranspose_norm A] at h
  exact h
end OAI.FiniteSieveRestriction
