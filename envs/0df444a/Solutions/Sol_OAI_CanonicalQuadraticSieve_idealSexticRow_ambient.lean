-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.idealSexticRow_ambient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:59:49.716546+00:00
-- url     : https://prove2.me/submissions/b816ec56-f097-461f-8934-75d93a0812b4

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Theorems.Thm_OAI_ConcretePrimeRowBridge_mem_idealSupport_iff


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
open scoped BigOperators
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (F G : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥) (hGp : ∀ I ∈ G, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hGg : ∀ I ∈ G, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hIF : I ∈ F) (hIG : I ∈ G) (z : O) :
    idealSexticRow F hFp hFg I z = idealSexticRow G hGp hGg I z := by
  let idx (i : primePool F) (hi : i ∈ idealSupport F I) : primePool G :=
    ⟨i.val, mem_primePool_iff.mpr ⟨I, hIG, (mem_idealSupport_iff F I i).mp hi⟩⟩
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_bij idx
  · intro i hi
    exact (mem_idealSupport_iff G I (idx i hi)).mpr ((mem_idealSupport_iff F I i).mp hi)
  · intro i hi j hj hij
    exact Subtype.ext (congrArg (fun k : primePool G => k.val) hij)
  · intro j hj
    let i : primePool F := ⟨j.val, mem_primePool_iff.mpr
      ⟨I, hIF, (mem_idealSupport_iff G I j).mp hj⟩⟩
    have hi : i ∈ idealSupport F I :=
      (mem_idealSupport_iff F I i).mpr ((mem_idealSupport_iff G I j).mp hj)
    exact ⟨i, hi, Subtype.ext rfl⟩
  · intro i hi
    rfl
end OAI.CanonicalQuadraticSieve
