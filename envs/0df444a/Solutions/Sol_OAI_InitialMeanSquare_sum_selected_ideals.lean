-- Prove2me | solution 1 for OAI.InitialMeanSquare.sum_selected_ideals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:31:49.618264+00:00
-- url     : https://prove2.me/submissions/315eb574-92de-4034-ab5d-3933f39f4e72

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealSupport_product_eq
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge
namespace OAI.InitialMeanSquare
theorem _root_.solution (F : Finset (Ideal O)) (hF : ∀I∈F,Squarefree I)
    (a : Ideal O→ℂ) :
    (∑I∈F,a I)=∑S∈(Finset.univ:Finset (primePool F)).powerset,
      if (∏i∈S,i.val)∈F then a (∏i∈S,i.val) else 0 := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun S _ => ∏i∈S,i.val)
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · intro S hS T hT he
    exact family_product_injective (fun i:primePool F => i.val) Subtype.val_injective he
  · intro I hI
    refine ⟨idealSupport F I,?_,idealSupport_product_eq F hI (hF I hI)⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    rwa [idealSupport_product_eq F hI (hF I hI)]
  · intro S hS
    rfl
end OAI.InitialMeanSquare
